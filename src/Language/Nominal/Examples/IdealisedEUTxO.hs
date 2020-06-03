{-|
Module      : Idealised EUTxO 
Description : Haskell rendering of the mathematical idealisation of the Extended UTxO model 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Haskell rendering of the <https://arxiv.org/abs/2003.14271 mathematical idealisation of the Extended UTxO model>. 
-}

{-# LANGUAGE ConstraintKinds            
           , DataKinds                  
           , DefaultSignatures          
           , DeriveAnyClass             
           , DeriveGeneric              
           , DerivingStrategies         
           , DerivingVia                
           , EmptyCase                   -- for \case {} in GHasInputPositions
           , LambdaCase                  -- for \case {} in GHasInputPositions
           , FlexibleInstances          
           , FlexibleContexts            -- so we can write `Swappable d`
           , FunctionalDependencies     
           , GeneralizedNewtypeDeriving 
           , IncoherentInstances         -- monoid instance of Maybe Chunk 
           , InstanceSigs               
           , MultiParamTypeClasses      
           , ScopedTypeVariables        
           , StandaloneDeriving         
           , TypeOperators              
           , UndecidableInstances       
#-}

{-# OPTIONS_GHC -fprint-explicit-foralls #-}  -- more detailed type information, along with :t +v <expr>

module Language.Nominal.Examples.IdealisedEUTxO 
    ( 
    -- * Types for inputs, outputs, and transaction lists
    -- $types
       Position, Input (..), Output (..), TransactionF (..), Transaction, Context,
    -- * Calculating input and output positions 
    -- $calculating
       HasInputPositions (..), HasOutputPositions (..),
    -- * Validators
    -- $validator
       Validator (..), ValTriv (..), Val (..), ValFin (..),
    -- * Chunks
    -- $chunks
       Chunk (..), transactionValid, singletonChunk, unsafeSingletonChunk, txListToChunk, nomTxListToNomChunk, nomTxListToChunk, 
    -- * Examples
    -- $examples
    exampleCh0, exampleCh1, exampleCh2, exampleCh12, exampleCh21, exampleCh12',
    -- * Unspent (dangling) elements: UTxO, UTxI, UTxC
    -- $unspent
    outputsOfTx, inputsOfTx, txPoint, contextsOfTx, utxosOfChunk, utxisOfChunk, contextPos, utxcsOfChunk,
    -- * Combining and extending chunks
    appendTxChunk, appendTxMaybeChunk, concatChunk, safeConcatChunk,
    -- * Splitting chunks up 
    genUnNomChunk, isPrefixChunk, chunkLength, chunkTail, chunkHead, warningNotChunkTail, chunkTakeEnd, subTxListOf, reverseTxsOf, chunkToHdTl, chunkToHdHdTl,
    -- * Blockchain
    Blockchain, getBlockchain, blockchain,   
    -- * Is Chunk / Blockchain check
    chunkBindingOK, chunkValidatorsOK, isChunk, isChunk', isBlockchain, isBlockchain', 
    -- * Intensional equality of 'Chunk'
    -- $intension
    IEq, equivChunk 
    -- * Tests
    -- $tests
    )
    where

import           Data.List                  as L
import           Data.List.NonEmpty         (NonEmpty (..))
import           Data.List.Unique 
import           Data.List.Extra            (disjoint, takeEnd)
import           Data.Maybe
import           Data.Functor               ((<&>)) 
import           Control.Monad              (guard, zipWithM) 
import qualified Data.Set                   as S
import           Foreign
import           GHC.Generics
import           GHC.Stack                  (HasCallStack)
import           Numeric.Partial.Monoid
import           Numeric.Partial.Semigroup

import           Language.Nominal.Utilities 
import           Language.Nominal.Name 
import           Language.Nominal.NameSet
import           Language.Nominal.Nom
import           Language.Nominal.Binder
import           Language.Nominal.Unify
import           Language.Nominal.Equivar



-- * Types for inputs, outputs, and transaction lists 
{- $types
These are the basic types of our development.

* A __'Position'__ is just an 'Atom' (a unique identifier).  It identifies a location on the blockchain.
* __'Input's__ point backwards towards outputs.  Inputs and outputs identify one another by position.
* __'Output's__ point wait for future inputs to point to them by naming the position they carry.  Outputs carry validators, to check whether they like any input that tries to point to them.
* A __'Transaction'__ is a list of inputs (pointing backwards) and a list of outputs (pointing forwards).
* A __'Context'__ is a transaction with a distinguished designated input, i.e. an input-in-context.  In fact, outputs validate contexts; this is what makes it EUTxO, for Extended UTxO, instead of just UTxO. 
* We also introduce the notion of __'Chunk'__, which is a valid list of transactions under a name-binding, and a notion of __UTxI__, meaning an input that does not refer to a preceding output in its chunk. 
* A __'Blockchain'__ is then a 'Chunk' with no UTxIs.  The benefit of working with Chunks as primitive is that valid Chunks form a monoid and are down-closed under taking sublists.  

These are all novel observations which are original to this development and the associated paper(s).
Then mathematically, the types below solve and make operational the following equations, parameterised over types @r@ and @d@ of /redeemer/s and /data/: 

@
Input       =  Position x r 
Output      =  d x Validator
Transaction =  Input-list x Output-list
Context     =  Input-nonempty-list x Output-list
Validator   <= (d x Context) -> Bool -- Val and ValFin are 
                                 -- two solutions to this subset inclusion
@

More exposition follows in the code.  See also the tests in "Language.Nominal.Properties.Examples.IdealisedEUTxOSpec":
-} 

-- | Positions are atoms.  These identify locations in a 'Chunk' or 'Blockchain'.
type Position             = Atom 
-- | An input has a position and a /redeemer/ @r@.  Think of the redeemer is a key which we use to unlock access to whatever output this input wants to connect to.  
--
-- Here @r@ is a type parameter, to be instantiated later.
data Input r              = Input Position r                       
   deriving stock (Show, Eq, Ord, Generic)
-- | An output has a position, a /datum/ @d@, and a /validator/ @v@.  
-- 
-- * Think of the /datum/ as a fragment of state data which is attached to this output.
-- * Think of the /validator/ as a machine which, if given a suitable redeemer (along with other stuff), with authorise or forbid access to this output.
-- 
-- @d@ and @v@ are type parameters, to be instantiated later.
data Output d v           = Output Position d v                    
   deriving stock (Show, Eq, Ord, Generic)
-- | A @TransactionF@ consists of an @f@ of inputs, and a list of outputs.  
-- 
-- Type parameters are:
--
-- * @f@ a parameter which can be instantiated to a type-constructor (<http://dev.stephendiehl.com/fun/001_basics.html#higher-kinded-types higher-kinded types>).  In this file, @f@ will be either list or nonempty list. 
-- * @r@ a parameter for the /redeemer/.
-- * @d@ a parameter for the /datum/.
-- * @v@ a parameter for the /validator/.
data TransactionF f r d v = Transaction (f (Input r)) [Output d v] 
   deriving stock (Generic)
-- A @Transaction@ is a @'TransactionF'@ over lists.  
-- 
-- Here @f@ is instantiated to the list type, so Transaction r d v = Transaction [Input r] [Output d v]. 
type Transaction          = TransactionF []            
-- A @Context@ is a @'TransactionF'@ over nonempty lists; the first element of the list of intputs is taken to be the distinguished "point" of the context. 
-- 
-- Here @f@ is instantiated to the nonempty list type, so Context r d v = Transaction (NonEmpty (Input r)) [Output d v]. 
type Context              = TransactionF NonEmpty

deriving stock instance (Eq r, Eq d, Eq v) => Eq (Transaction r d v)  
deriving stock instance (Eq r, Eq d, Eq v) => Eq (Context r d v)

-- With @ConstraintKinds@, the type synonym @KSupport Tom@ is allowed in the assumptions, but must be spelled out in the head.  
instance Support r => KSupport Tom (Input r) where    
instance (Support d, Support v) => KSupport Tom (Output d v) where
instance (Support d, Support r, Support v) => KSupport Tom (Context r d v)
instance (Support d, Support r, Support v) => KSupport Tom (Transaction r d v)

instance Swappable r => Swappable (Input r) 
instance (Swappable d, Swappable v) => Swappable (Output d v)
instance (Swappable r, Swappable d, Swappable v) => Swappable (Transaction r d v)
instance (Swappable r, Swappable d, Swappable v) => Swappable (Context r d v)

instance UnifyPerm r => KUnifyPerm Tom (Input r)
instance (UnifyPerm d, UnifyPerm v) => KUnifyPerm Tom (Output d v)
instance (UnifyPerm d, UnifyPerm r, UnifyPerm v) => KUnifyPerm Tom (Context r d v)
instance (UnifyPerm d, UnifyPerm r, UnifyPerm v) => KUnifyPerm Tom (Transaction r d v)

deriving instance (Show (f (Input r)), Show d, Show v) => Show (TransactionF f r d v)


-- * Calculating input and output positions 

{- $calculating
A technical matter: we exploit the Haskell typeclass mechanisms to set up some machinery to calculate the input and output positions mentioned in a data structure.  This resembles the development of @'Support'@, but specialised to intputs and outputs.
-}
 
-- | A typeclass for types for which we can calculate __input positions__.
--
-- @'inputPositions'@ just traverses @a@'s type structure, looking for subtypes of the form @'Input' p _@, and collecting the @p@s.
-- The only interesting instance is that of @'Nom' a@, where bound @p@s get garbage-collected. 
class HasInputPositions a where
    inputPositions :: a -> [Position]
    default inputPositions :: (Generic a, GHasInputPositions (Rep a)) => a -> [Position]
    inputPositions = gInputPositions . from

instance HasInputPositions (Input r) where
   inputPositions (Input p _)  = [p]

instance HasInputPositions (Output d v) where
   inputPositions Output {} = []

instance (HasInputPositions a, HasInputPositions b) => HasInputPositions (a,b)
instance HasInputPositions a => HasInputPositions [a]
instance HasInputPositions a => HasInputPositions (NonEmpty a)
instance HasInputPositions (Transaction r d v) where
   inputPositions (Transaction is _) = inputPositions is -- Not boilerplate: must not count inputs that appear in the list of outputs. 

-- | A typeclass for types for which we can calculate __output positions__. 
--
-- @'outputPositions'@ just traverses @a@'s type structure, looking for subtypes of the form @'Output' p _ _@, and collecting the @p@s. 
-- The only interesting instance is that of @'Nom' a@, where bound @p@s get garbage-collected. 
class HasOutputPositions a where
    outputPositions :: a -> [Position]
    default outputPositions :: (Generic a, GHasOutputPositions (Rep a)) => a -> [Position]
    outputPositions = gOutputPositions . from

instance HasOutputPositions (Input r) where
   outputPositions (Input _ _) = [] 

instance HasOutputPositions (Output d v) where
   outputPositions (Output p _ _) = [p]

instance (HasOutputPositions a, HasOutputPositions b) => HasOutputPositions (a,b)
instance HasOutputPositions a => HasOutputPositions [a]
instance HasOutputPositions a => HasOutputPositions (NonEmpty a)
instance HasOutputPositions (Transaction r d v) where
   outputPositions (Transaction _ os) = outputPositions os  


instance (Swappable a, HasOutputPositions a) => HasOutputPositions (Nom a) where
   outputPositions = resAppC outputPositions 

-- * Unspent (dangling) elements: UTxO, UTxI, UTxC
{- $unspent

We care about which inputs point to earlier outputs, and which outputs point to later inputs, and which do not.  Specifically, we introduce three functions:

* @'utxosOfChunk'@, calculating those outputs that do not point to a later input in a chunk.  This is standard (albeit for chunks, not blockchains).
* @'utxisOfChunk'@, calculating those inputs that do not point to an earlier output in a chunk.  While not complicated to define, the explicit emphasis on this as an interesting value to calculate comes from our shift from working with /'Blockchain's/ to working with /'Chunk's/.
* @'utxcsOfChunk'@, calculating those contexts (inputs-in-their-transaction) that do not point to an earlier output in a chunk.  Again, the explicit emphasis on this as an interesting value to calculate comes from our shift from working with /'Blockchain's/ to working with /'Chunk's/.
-}

-- | Return the output-list of a 'Transaction'.
outputsOfTx :: Transaction r d v -> [Output d v]
outputsOfTx (Transaction _ os) = os

-- | Return the input-list of a 'Transaction'.
inputsOfTx :: Transaction r d v -> [Input r]
inputsOfTx (Transaction is _) = is

-- | Point a transaction at @p@ 
txPoint :: Support r => Transaction r d v -> Position -> Context r d v
txPoint (Transaction is os) p = Transaction (atomPoint p is) os
 
-- | Form the contexts of a 'Transaction'.
contextsOfTx :: Support r => Transaction r d v -> [Context r d v]
contextsOfTx tx = txPoint tx <$> inputPositions tx

-- | Calculate __unspent outputs__.
-- 
-- We tell an output is unspent when its position isn't bound in the enclosing 'Nom' name-context.
utxosOfChunk :: Validator r d v => Chunk r d v -> [Output d v]
utxosOfChunk = resAppC $ concatMap outputsOfTx 

-- | Calculate __unspent inputs__. 
--
-- Because we're dealing with transaction lists, we care about dangling /inputs/ (which we call UTxIs) as well as UTxOs.
utxisOfChunk :: Validator r d v => Chunk r d v -> [Input r]
utxisOfChunk = resAppC $ concatMap inputsOfTx -- accumulate inputs listwise.  The 'restrict' implicit in the use of 'resAppC' filters out outputs that mention bound names.

-- | What's the point of my context?   The position @p@ of the first element of the input list of a context is deemed to be the "call site" from which the context tries to find a preceding output (with position @p@) in its @'Chunk'@. 
contextPos :: Context r d v -> Position
contextPos (Transaction (Input p _ :| _) _) = p 

-- | Calculate unspent __input contexts__. 
--
-- Because we're dealing with transaction lists, we care about dangling /contexts/ (which we call UTxCs). 
utxcsOfChunk :: Validator r d v => Chunk r d v -> Nom [Context r d v] -- the top-level Nom binding here stores the bound names of the chunk, i.e. those participating in an Input-Output binding within the chunk.
utxcsOfChunk = nomApp $ \ps txs ->  
    L.filter (\c -> contextPos c `notElem` ps) (concatMap contextsOfTx txs)


-- * Validators

{- $validator
Our types for 'Output', 'Transaction', and 'Context' are parameterised over a type of validators.  We now build a typeclass 'Validator' to hold validators, and build two instances 'Val' and 'ValFin': 

* 'Val' is just a type of functions wrapped up in a wrapper saying "I am a validator".  If you have a function and it's a validator, you can put it here.
* 'ValFin' is an /equivariant orbit-finite map/ type, intended to be used with the machinery in "Language.Nominal.Equivar".  A significant difference from 'Val' is that 'ValFin' can support equality 'Eq'. 
-}

-- | A typeclass for __validators__.  A validator is an equivariant object that takes a datum and a @'Context'@, and returns a @'Bool'@.
class (Support r, Support d, Support v) => Validator r d v | v -> r d where  
    validate :: v -> d -> Context r d v -> Bool

-- | A type for trivial validators that always return true
data ValTriv r d = ValTriv
    deriving (Eq, Ord, Show, Read)

deriving via Nameless (ValTriv r d) instance Swappable (ValTriv r d)
deriving via Nameless (ValTriv r d) instance KUnifyPerm Tom (ValTriv r d)
deriving via Nameless (ValTriv r d) instance KSupport Tom (ValTriv r d)

instance (Support r, Support d) => Validator r d (ValTriv r d) where
    validate ValTriv _ _ = True

-- | A 'Val' is an equivariant predicate on datum and context.  
-- For convenience we make it @'Nameless'@. 
newtype Val r d = Val (EvFun (d, Context r d (Val r d))  Bool)
    deriving newtype IEq 
    deriving (Swappable, KRestrict Tom, KSupport Tom) via Nameless (Val r d)
instance Show (Val r d) where
    show = const "Val"

-- | 'Val' is a 'Validator'
instance (Support r, Support d) => Validator r d (Val r d) where
    validate (Val f) d c = runEvFun f (d, c)

-- | A 'ValFin' is an equivariant orbit-finite predicate on datum and context.  
-- For convenience we make it @'Nameless'@. 
newtype ValFin r d = ValFin (EvFinMap (d, Context r d (ValFin r d)) Bool)
    deriving newtype (Generic, Show)
    deriving (Swappable, KRestrict Tom, KSupport Tom) via Nameless (ValFin r d)

instance (UnifyPerm r, UnifyPerm d) => Eq (ValFin r d) where
    ValFin f == ValFin g = f == g  

deriving via Nameless (ValFin r d) instance (UnifyPerm r, UnifyPerm d) => KUnifyPerm Tom (ValFin r d) -- @ValFin r d@ is assumed nameless

instance (UnifyPerm r, UnifyPerm d) => Validator r d (ValFin r d) where
    validate (ValFin f) d c = f $$ (d, c)  



-- * Chunks

{- $chunks
A @'Chunk'@ is a valid list of transactions in a local name-binding context. 
Validity is enforced by the constructor @'appendTxChunk'@, which imposes a validity check.

@'Chunk'@, not @'Blockchain'@, is the fundamental abstraction of our development.
A blockchain is just a chunk without any UTxIs (see @'isBlockchain'@ and @'utxisOfChunk'@); conversely a chunk is "like a blockchain, but may have UTxIs as well as UTxOs". 

Chunks have properties that blockchains don't.  For instance: 

* If we slice a chunk up into pieces, we get another chunk. 
* A subchunk of a chunk is still a chunk.

In contrast, if we slice up a blockchain, we get chunks, not blockchains. 
Thus, blockchains are not naturally compositional and structured in the way that chunks are.

This is a benefit of making the datatype of /chunks/ our primary abstraction.
-}

-- | A @'Chunk'@ is a valid list of transactions in a local name-binding context.  Think of it as a generalisation of blockhains that allows UTxIs (unspent transaction /inputs/). 
newtype Chunk r d v = Chunk {chunkToTxList :: Nom [Transaction r d v]}
    deriving (Show, Generic) 

-- equivalent formulation
-- instance (Swappable r, Swappable d, Swappable v) => Swappable (Chunk r d v) where
--   kswp n1 n2 (Chunk p) = Chunk (kswp n1 n2 p)
deriving newtype instance (Swappable r, Swappable d, Swappable v) => Swappable (Chunk r d v)
deriving newtype instance (UnifyPerm r, UnifyPerm d, UnifyPerm v) => KUnifyPerm Tom (Chunk r d v)
deriving newtype instance (Support r, Support d, Support v) => KSupport Tom (Chunk r d v) -- could also use deriving via BinderSupp, but since Chunk is just a newtype wrapper around a Nom, a deriving newtype seems more direct.


-- | Acts on a @'Chunk'@ by unpacking it as a transaction-list and a list of locally bound atoms, and applying a function. 
instance Validator r d v => Binder (Chunk r d v) [Atom] [Transaction r d v] Tom where 
   (@@) :: Chunk r d v -> ([Atom] -> [Transaction r d v] -> b) -> Nom b -- ^ The destructor.  
   (@@) (Chunk nomtxs) = (@@) nomtxs 
   resMay :: [Atom] -> [Transaction r d v] -> Maybe (Chunk r d v) -- ^ The constructor.  Because chunks are subject to validation conditions, not every list of transactions is a valid chunk.  Thus, we define 'resMay' instead of '(@>)'. 
   resMay = const txListToChunk

-- | Chunk equality tests for equality, with permutative unification on the local names
--
-- @(==) = unifiablePerm@ would be wrong; we should only unify /bound/ atoms.
--
-- Note: @'Ren'@ equality compares nubs (non-identity mappings) 
instance (UnifyPerm r, UnifyPerm d, UnifyPerm v, Validator r d v) => Eq (Chunk r d v) where
   ch1 == ch2 = 
      ch1 @@. \as1 txs1 ->  -- unpack the local bindings of both chunks
      ch2 @@. \as2 txs2 ->
         idRen == renRemoveBlock (as1 ++ as2) (unifyPerm txs1 txs2) -- unify txs1 with txs2 and make sure all renamings are only on the bound atoms 

-- | A @'transaction'@ is valid if (at least) all positions are disjoint 
transactionValid :: Transaction r d v -> Bool
transactionValid (Transaction is os) = allUnique $ inputPositions is ++ outputPositions os

-- | Tries to create a valid @'Chunk'@ from a single @'Transaction'@.  If it fails, we get 'Nothing'.
singletonChunk :: Transaction r d v -> Maybe (Chunk r d v)
singletonChunk tx = toMaybe (transactionValid tx) $ Chunk (return [tx])

-- | Creates a valid @'Chunk'@ from a single @'Transaction'@.
-- If it fails (because the transaction is invalid), it raises and error.
unsafeSingletonChunk :: HasCallStack => Transaction r d v -> Chunk r d v
unsafeSingletonChunk = fromMaybe err . singletonChunk
  where
    err = error "singletonChunk: invalid transaction"

-- | Combine a list of transactions into a @'Chunk'@.  Return @'Nothing'@ if list does not represent a valid chunk.
txListToChunk :: Validator r d v => [Transaction r d v] -> Maybe (Chunk r d v)
txListToChunk = foldMap singletonChunk -- relies on Monoid action on Maybe Chunk 


-- | Combines a list of @'Transaction'@s in a @'Nom'@ binding context, into a @'Chunk'@.
--
-- * Gathers any excess positions (those not linking inputs to outputs) in the @'Nom'@ binding.
-- * Returns @'Nothing'@ if the transaction list doesn't form a valid @'Chunk'@.
nomTxListToNomChunk :: (HasCallStack, Validator r d v) 
   => Nom [Transaction r d v] -> Maybe (Nom (Chunk r d v))
nomTxListToNomChunk ntxs = transposeNomMaybe $ txListToChunk <$> ntxs  

-- | Combines a list of transactions in a binding context, into a Chunk, with a check that no excess positions are bound.  Returns Nothing if check fails.
nomTxListToChunk :: (HasCallStack, Validator r d v) 
   => Nom [Transaction r d v] -> Maybe (Chunk r d v)
nomTxListToChunk ntxs = do -- Maybe monad
   n <- nomTxListToNomChunk ntxs 
   guard (isTrivialNomBySupp n) 
   return $ unNom n   

-- * Examples 

{- $examples

Some example chunks for the reader's convenience and for unit tests.  

* @exampleCh0@ is the chunk containing a trivial transaction with no inputs and no outputs (and one locally bound name, which is not used). 
* @exampleCh1@ is an output with trivial validator.  Wrapped in a Nom binding to store its position.
* @exampleCh2@ is an input.  Wrapped in a Nom binding to store its position.
* @exampleCh12@ is @exampleCh1 <> exampleCh 2@.  Note their positions don't line up.  Also has overbinding! 
* @exampleCh21@ is @exampleCh1 <> exampleCh 2@ with positions lined up. 
* @exampleCh12'@ is @exampleCh2 <> exampleCh 1@ with positions lined up.  Name-clash: fails.

See 'isChunk' and 'isBlockchain' for unit tests.

-}

-- | Example chunk 0: "Chunk [p] [Transaction [] []]"
--
-- A chunk containing an empty transaction, with a vacuous binding by some @p@.
--
-- Is chunk.  Is blockchain.
--
-- >>> isChunk exampleCh0
-- True
--
-- >>> isBlockchain exampleCh0
-- True
exampleCh0 :: Chunk Int Int (ValTriv Int Int) 
exampleCh0 = newA $ \(_p :: Atom) -> fromJust . singletonChunk $ Transaction [] [] 

-- | Example chunk 1: "Chunk [p] [Transaction [] [Output p 0 (const True)]]"
--
-- One output with datum 0 and trivial validator that always returns 'True'.  
--
-- Is chunk.  Is blockchain.
exampleCh1 :: Nom (Chunk Int Int (ValTriv Int Int)) 
exampleCh1 = freshAtom <&> \p -> fromJust $ singletonChunk $ Transaction [] [Output p 0 ValTriv] 

-- | Example chunk 2: "Chunk [p] [Transaction [Input p 0] []]"
--
-- One input with redeemer 0.  
--
-- Is chunk.  Is not blockchain.
exampleCh2 :: Nom (Chunk Int Int (ValTriv Int Int)) 
exampleCh2 = freshAtom <&> \p -> fromJust $ singletonChunk $ Transaction [Input p 0] [] 

-- | Example chunk obtained by concatenating chunks 1 and 2.  Concat succeeds but positions don't line up.  Is not blockchain, and also is not valid chunk because of overbinding.
--
-- "Chunk [p1, p2] [Transaction [Input p2 0] [], Transaction [] [Output p1 0 (const True)])]"
--
-- (Note: we write lists with their head to the left, so time flows from right to left above.)
--
-- >>> isChunk exampleCh12
-- False
exampleCh12 :: (Chunk Int Int (ValTriv Int Int)) 
exampleCh12 = fromJust . unNom $ do -- Nom monad
   ch1 <- exampleCh1
   ch2 <- exampleCh2
   return $ concatChunk ch1 ch2 

-- | Example chunk obtained by combining chunks 1 and 2, now on same name so input points to output.  
-- 
-- "Chunk [p] [Transaction [Input p 0] [], Transaction [] [Output p 0 (const True)])]"
--
-- (Note: we write lists with their head to the left, so time flows from right to left above.)
--
-- Is chunk.  Is blockchain.
exampleCh21 :: (Chunk Int Int (ValTriv Int Int)) 
exampleCh21 = fromJust . unNom $ do -- Nom monad
   ch1 <- exampleCh1
   ch2 <- exampleCh2
   let [a] = S.toList $ supp ch1 
   let [b] = S.toList $ supp ch2 
   return $ concatChunk ch2 (swp a b ch1) 

-- | Example chunk obtained by combining chunks 1 and 2, on same name.  But output comes /after/ input, not before.  Concat fails because nameclash is detected.
exampleCh12' :: Maybe (Chunk Int Int (ValTriv Int Int)) 
exampleCh12' = unNom $ do -- Nom monad
   ch1 <- exampleCh1
   ch2 <- exampleCh2
   let [a] = S.toList $ supp ch1 
   let [b] = S.toList $ supp ch2 
   return $ concatChunk ch1 (swp a b ch2) 

-- * Combining and extending chunks

-- | Calculate the input and output positions
positionsOfTxs :: [Transaction r d v] -> ([Position], [Position])
positionsOfTxs txs = (inputPositions txs, outputPositions txs) 
 
-- | @'appendTxChunk' tx txs@ adds @tx@ to @txs@, provided that:
--
-- * @tx@ is valid
-- * there is no position name-clash and 
-- * validators are happy.
--
-- This is the core of this file.  In a certain sense, everything is just different ways of wiring into this function.
appendTxChunk :: (HasCallStack, Validator r d v) => Transaction r d v -> Chunk r d v -> Maybe (Chunk r d v)  
appendTxChunk tx ch = ch @@. \_ txs -> -- use of '@@.' here ensures that any atoms bound in ch stay bound in result.  However, the extra atoms in bn below, get added to binding.
   let (txIns,  txOuts ) = positionsOfTxs [tx] 
       (txsIns, txsOuts) = positionsOfTxs txs
       bn = intersect txIns txsOuts -- the inputs of @tx@ that point to outputs in @txs@ and so should get bound
   in
   toMaybe 
      (   transactionValid tx     -- tx is valid 
       && disjoint txOuts txsOuts -- no outputs in tx clash with outputs in txs
       && disjoint txOuts txsIns  -- no outputs in tx clash with inputs in txs
       && disjoint txIns  txsIns  -- no inputs in tx clash with inputs in txs
       && all validate' bn)       -- all validators happy with context   
      (Chunk $ bn @> tx : txs)    -- all OK?  then push tx 
 where
   validate' :: Position -> Bool
   validate' pos =
      let Transaction ins outs = tx
          utxos                = utxosOfChunk ch 
          Output _ datum v     = iota (\(Output p _ _) -> p == pos) utxos
          context              = Transaction (atomPoint pos ins) outs
      in  validate v datum context

-- | Version of @'appendTxChunk'@ that acts directly on @Maybe (Chunk r d v)@.
appendTxMaybeChunk :: Validator r d v => Transaction r d v -> Maybe (Chunk r d v) -> Maybe (Chunk r d v)
appendTxMaybeChunk = (=<<) . appendTxChunk 
 
-- | Restrict atoms in a 'Chunk'.
instance (Swappable r, Swappable d, Swappable v) => KRestrict Tom (Chunk r d v) where 
   restrict atms (Chunk x) = Chunk $ restrict atms x -- Relies on restrict being monadic on Maybe


-- | Concatenate two @'Chunk'@s, merging their binding contexts in a capture-avoiding manner.
-- If concatenation is impossible (e.g. because validation fails), defaults to @Chunk Nothing@.
--
-- __Note:__ No explicit checks are made here that inputs are valid chunks.  In particular, no overbinding protection (overbinding = Nom binder in Chunk binds excess positions not involved in UTxO-UTxI linkage).  If you want such checks, look at 'isChunk' and 'isBlockchain'.
--
-- Works by unpacking first chunk as a list of transactions and appending them to 'Just' the second argument.  Local binding of first chunk gets carried over automatically; new local bindings may get generated during the append.
concatChunk :: Validator r d v => Chunk r d v -> Chunk r d v -> Maybe (Chunk r d v)
concatChunk ch1 ch2 = resAppC (foldr appendTxMaybeChunk (Just ch2)) ch1 


-- | A version of 'concatChunk' that performs explicit validity checks on its inputs and result. 
safeConcatChunk :: Validator r d v => Chunk r d v -> Chunk r d v -> Maybe (Chunk r d v)
safeConcatChunk ch1 ch2 = 
   guard (isChunk ch1 && isChunk ch2 && isJust (concatChunk ch1 ch2)) 
   >> (concatChunk ch1 ch2) 

-------------------------------------
----- Algebraic properties of Chunk and Maybe Chunk


instance Validator r d v => PartialSemigroup (Chunk r d v) where
   padd = concatChunk

-- | Chunk forms a partial monoid
instance Validator r d v => PartialMonoid (Chunk r d v) where
   pzero = Chunk $ return []


instance Validator r d v => Semigroup (Maybe (Chunk r d v)) where
   mch <> mch' = do -- Maybe monad
      ch  <- mch
      ch' <- mch'
      concatChunk ch ch'

-- | Maybe Chunk forms a monoid, with unit being the empty chunk.
instance Validator r d v => Monoid (Maybe (Chunk r d v)) where
   mempty  = Just . Chunk . return $ []
   mappend = (<>)
-- TODO: why no overlapping instance error messages with rule from Data.Monoid?



-- * Splitting chunks up 

-- | For debugging
genUnNomChunk :: Validator r d v => Chunk r d v -> Chunk r d v
genUnNomChunk = genAppC $ Chunk . return 

-- | Check whether one chunk is a prefix of another.  See @'chunkTail'@ to understand why the @'Nom'@ binding on the first argument is required.
isPrefixChunk :: (UnifyPerm r, UnifyPerm d, UnifyPerm v, Validator r d v) => Nom (Chunk r d v) -> Chunk r d v -> Bool  
isPrefixChunk ch1' ch2 =     
   ch1' @@. \as  ch1  ->   -- as = local names in putative prefix 
   ch1  @@. \as1 txs1 ->  
   ch2  @@. \as2 txs2 -> 
      case evPrefixRen txs1 txs2 of 
         Ren Nothing -> False 
         r           -> supp r `S.isSubsetOf` S.fromList (as ++ as1 ++ as2) 


-- | Calculate the length of a Chunk
chunkLength :: Validator r d v => Chunk r d v -> Int 
chunkLength = resAppC L.length 


-- | Calculate the head of a chunk.  
chunkHead :: (UnifyPerm r, UnifyPerm d, Validator r d v) => Chunk r d v -> Maybe (Nom (Transaction r d v))
chunkHead ch = transposeNomMaybe $ nomAppC safeHead ch 


-- | Calculate the tail of a chunk.  Two monads here:
--
-- * @'Maybe'@, because the underlying list of transactions might be empty and so have no tail.  And if it's not empty ...
--
-- * @'Nom'@ ... to bind the names of any positions in newly-exposed UTxOs.
chunkTail :: (UnifyPerm r, UnifyPerm d, Validator r d v) => Chunk r d v -> Maybe (Nom (Chunk r d v))
chunkTail ch = transposeNomMaybe $ nomAppC ((=<<) txListToChunk . safeTail) ch 
-- chunkTail ch = transposeNomMaybe $ nomAppC (\txs -> safeTail txs >>= txListToChunk) ch 


-- | Compare the code for this function with the code for @'chunkTail'@.  
-- It looks plausible ... but it's wrong.
--
-- It looks like it returns the tail of a chunk, and indeed it does.  However, the result is not a chunk because positions get exposed. 
--
-- See the test 'Language.Nominal.Properties.Examples.IdealisedEUTxOSpec.prop_warningNotChunkTail_is_not_chunk'.
warningNotChunkTail :: (UnifyPerm r, UnifyPerm d, Validator r d v) => Chunk r d v -> Maybe (Chunk r d v)
warningNotChunkTail = genAppC $ \txs -> (Chunk . return) <$> safeTail txs 
{-- warningNotChunkTail ch = ch @@. \_ txs -> case txs of
    []         -> Nothing
    (_ : txs') -> Just $ Chunk $ return txs'  --}


-- | @'take'@, for chunks.  The @'Nom'@ binding captures any dangling UTxOs or UTxIs that are left after truncating the chunk. 
chunkTakeEnd :: (UnifyPerm r, UnifyPerm d, Validator r d v) => Int -> Chunk r d v -> Nom (Chunk r d v)
chunkTakeEnd i ch = fromJust . nomTxListToNomChunk $ takeEnd i <$> chunkToTxList ch 


-- | List of subchunks.  @'Nom'@ binding is to capture dangling UTxOs or UTxIs.
subTxListOf :: (UnifyPerm r, UnifyPerm d, Validator r d v) => Chunk r d v -> Nom [[Transaction r d v]] 
subTxListOf = nomAppC subsequences 


-- | Take a chunk and reverse its transactions.  Usually this will result in an invalid chunk, in which case we get @Nothing@.  
-- Used for testing. 
reverseTxsOf :: (UnifyPerm r, UnifyPerm d, Validator r d v) => Chunk r d v -> Maybe (Chunk r d v) 
reverseTxsOf = nomTxListToChunk . nomAppC L.reverse 

-- | Split a chunk into a head and a tail.
chunkToHdTl :: Validator r d v => Chunk r d v -> Maybe (Nom (Transaction r d v, Chunk r d v))
chunkToHdTl (Chunk x') = transposeNomMaybe $ x' @@ \_ x -> case x of
   (tx:txs) -> return (tx, fromJust $ txListToChunk txs)
   []       -> Nothing

-- | Split a chunk into a head and a head and a tail.
chunkToHdHdTl :: Validator r d v => Chunk r d v -> Maybe (Nom (Transaction r d v, Transaction r d v, Chunk r d v))
chunkToHdHdTl (Chunk x') = transposeNomMaybe $ x' @@ \_ x -> case x of
   (tx1:tx2:txs) -> return (tx1, tx2, fromJust $ txListToChunk txs)
   _             -> Nothing


-- * Blockchain 

-- | A blockchain is a /valid/ @'Chunk'@, with no unspent inputs.
newtype Blockchain r d v = Blockchain {getBlockchain :: Chunk r d v}
    deriving (Show, Generic)

instance (Swappable r, Swappable d, Swappable v) => Swappable (Blockchain r d v) 
instance (Support r, Support d, Support v) => KSupport Tom (Blockchain r d v) 
instance (UnifyPerm r, UnifyPerm d, UnifyPerm v) => KUnifyPerm Tom (Blockchain r d v) 

-- | Smart constructor for a @'Blockchain'@. 
-- Ensures only valid blockchains are constructed, by testing for @'isBlockchain'@.
blockchain :: (HasCallStack, Validator r d v) => Chunk r d v -> Blockchain r d v  
blockchain c
    | isBlockchain c = Blockchain c
    | otherwise      = error ("blockchain: invalid chunk or dangling inputs") 


-- * Is Chunk / Blockchain check 

-- | Check that the correct atoms are bound in a 'Chunk'.
chunkBindingOK :: Validator r d v => Chunk r d v -> Bool 
chunkBindingOK = resApp $ \ps txs -> let (ips, ops) = positionsOfTxs txs in 
   ps `intersect` (ips ++ ops) == ips `intersect` ops 

-- | Check that validators are happy, by taking a 'Chunk' apart and putting it together again.
chunkValidatorsOK :: Validator r d v => Chunk r d v -> Bool 
chunkValidatorsOK = resAppC $ isJust . txListToChunk   -- take it apart and put it together with transaction validation 

-- | Is this a valid chunk?  ('exampleCh1', 'exampleCh2', 'exampleCh12', 'exampleCh21') 
--
-- >>> resAppC isChunk exampleCh1
-- True 
--
-- >>> resAppC isChunk exampleCh2
-- True 
--
-- >>> isChunk exampleCh12
-- False
--
-- >>> isChunk exampleCh21
-- True
isChunk :: Validator r d v => Chunk r d v -> Bool 
isChunk ch = chunkBindingOK ch && chunkValidatorsOK ch 

-- | Is this a valid chunk?  Test by splitting it into a transaction list and putting it back together again. 
--
isChunk' :: (Validator r d v, UnifyPerm r, UnifyPerm d, UnifyPerm v) => Chunk r d v -> Bool 
isChunk' ch = Just ch == genAppC txListToChunk (chunkToTxList ch) 

-- | A blockchain is a valid 'Chunk' with no UTxI (unspent transaction /inputs/).  ('exampleCh1', 'exampleCh2', 'exampleCh12', 'exampleCh21') 
--
-- >>> isBlockchain exampleCh0
-- True
--
-- >>> resAppC isBlockchain exampleCh1
-- True
--
-- >>> resAppC isBlockchain exampleCh2
-- False 
--
-- >>> isBlockchain exampleCh12
-- False 
--
-- >>> isBlockchain exampleCh21
-- True 
isBlockchain :: Validator r d v => Chunk r d v -> Bool
isBlockchain ch = (L.null . utxisOfChunk) ch  -- no dangling inputs
               && isChunk ch                  -- is a valid chunk (e.g. no overbinding) 


-- | Blockchain check for 'Maybe' a 'Chunk'.
isBlockchain' :: Validator r d v => Maybe (Chunk r d v) -> Bool
isBlockchain' mch = (isBlockchain <$> mch) == Just True




-- * Intensional equality of 'Chunk' 

{- $intension
Modelled on <https://web.archive.org/web/20200405185005/https://mail.haskell.org/pipermail/haskell-cafe/2004-December/007766.html a post by Oleg Kiselyov>
An intensional equality allows us to compare 'Chunk's for equality of UTxOs, even if the type of validators does not have an 'Eq' instance.

We don't do this at the moment (we use 'ValFin' instead), but we still provide the facility in case it is useful for a user running e.g. QuickCheck tests where we care that structure gets put in the right place and assembled in the right ways, without caring too much about executing that structure for values of specific interest. 
-}

class IEq a where
    iEq :: a -> a -> IO Bool  
    default iEq :: Eq a => a -> a -> IO Bool
    iEq x y = return $ x == y 

instance IEq (a -> b) where
   iEq f g = do -- IO monad     
      pf <- newStablePtr f  -- fetch pointer to f
      pg <- newStablePtr g  -- and to f'
      let result = pf == pg -- equal?
      freeStablePtr pf      -- free the pointers
      freeStablePtr pg
      return result

instance IEq a => IEq [a] where
   iEq la la' = and <$> zipWithM iEq la la'

deriving newtype instance IEq (KEvFun k a b)
deriving anyclass instance Eq r => IEq (Input r)

-- | Equality on validators is intensional; (Validator f == Validator f') when f and f' happen to point to the same bit of memory when the equality runs. 
-- Thus if iEq f f' returns True this means that f and f' represent the same mathematical function, and indeed are also the same code.
-- If iEq f f' returns False this does not mean that f and f' represent distinct mathematical functions.
-- It just means they were represented by distinct code when iEq is called.  
-- This may be useful for running tests where we check that gobs of code get put in the right places and assembled in the right ways, without necessarily caring to execute them (or even without necessarily instantiating executable values). 
-- instance IEq Value where
instance (Eq d, IEq v) => IEq (Output d v) where
   iEq (Output p d vd) (Output p' d' vd') = do -- IO monad
      eqvd <- iEq vd vd'  -- check everything is intensionally equal
      return $ p == p' && eqvd && d == d'

-- | Intensional equality 
equivChunk :: (Eq r, Eq d, IEq v, Validator r d v) => Chunk r d v -> Chunk r d v -> IO Bool
equivChunk txlist1 txlist2 = and <$> sequence 
   [ utxosOfChunk txlist1 `iEq` utxosOfChunk txlist2 
   , utxisOfChunk txlist1 `iEq` utxisOfChunk txlist2
   ]


-- * Generics support for @'HasInputPositions'@

class GHasInputPositions f where
    gInputPositions :: f x -> [Position]

instance GHasInputPositions V1 where
    gInputPositions = \case {}  -- uses EmptyCase and LambdaCase.  Avoids hlint parse issue. 
 
instance GHasInputPositions U1 where
    gInputPositions U1 = []

instance HasInputPositions c => GHasInputPositions (K1 i c) where
    gInputPositions = inputPositions . unK1

instance (GHasInputPositions f, GHasInputPositions g) => GHasInputPositions (f :*: g) where
    gInputPositions (x :*: y) = gInputPositions x ++ gInputPositions y

instance (GHasInputPositions f, GHasInputPositions g) => GHasInputPositions (f :+: g) where
    gInputPositions (L1 x) = gInputPositions x
    gInputPositions (R1 y) = gInputPositions y

instance GHasInputPositions f => GHasInputPositions (M1 i c f) where
    gInputPositions = gInputPositions . unM1

-- * Generics support for @'HasOutputPositions'@

class GHasOutputPositions f where
    gOutputPositions :: f x -> [Position]

instance GHasOutputPositions V1 where
    gOutputPositions = \case {}  -- uses EmptyCase and LambdaCase.  Avoids hlint parse issue. 


instance GHasOutputPositions U1 where
    gOutputPositions U1 = []

instance HasOutputPositions c => GHasOutputPositions (K1 i c) where
    gOutputPositions = outputPositions . unK1

instance (GHasOutputPositions f, GHasOutputPositions g) => GHasOutputPositions (f :*: g) where
    gOutputPositions (x :*: y) = gOutputPositions x ++ gOutputPositions y

instance (GHasOutputPositions f, GHasOutputPositions g) => GHasOutputPositions (f :+: g) where
    gOutputPositions (L1 x) = gOutputPositions x
    gOutputPositions (R1 y) = gOutputPositions y

instance GHasOutputPositions f => GHasOutputPositions (M1 i c f) where
    gOutputPositions = gOutputPositions . unM1

{- $tests Property-based tests are in "Language.Nominal.Properties.Examples.IdealisedEUTxOSpec". -}
