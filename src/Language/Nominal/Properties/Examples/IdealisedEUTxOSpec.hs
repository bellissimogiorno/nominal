{-| 
__Please read the source code to view the tests.__
-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Language.Nominal.Properties.Examples.IdealisedEUTxOSpec
    where

import Control.Monad                              (replicateM)
import Data.List.NonEmpty                         (NonEmpty (..))
import Data.Maybe                                 (fromJust, isJust)
import Data.Proxy                                 (Proxy (..))
import qualified Data.Set as S 
import GHC.Generics
import Numeric.Partial.Semigroup
import Numeric.Partial.Monoid
import Test.QuickCheck
import Type.Reflection                           

import Language.Nominal.Examples.IdealisedEUTxO
-- import Language.Nominal.Name                      (Smallish (..))
import Language.Nominal.NameSet
import Language.Nominal.Properties.SpecUtilities  (genEvFinMap)
import Language.Nominal.Properties.UnifySpec      ()
import Language.Nominal.Unify
import Language.Nominal.Equivar
import Language.Nominal.Nom

instance Arbitrary r => Arbitrary (Input r) where
    arbitrary = Input <$> arbitrary <*> arbitrary
    shrink (Input p r) = Input p <$> shrink r -- only shrinking the redeemer, not the position

instance Arbitrary (ValTriv r d) where
    arbitrary = return ValTriv
    shrink = const []

instance (Eq r, UnifyPerm r, Arbitrary r, Eq d, UnifyPerm d, Arbitrary d) => Arbitrary (ValFin r d) where
    arbitrary = ValFin <$> genEvFinMap (scale (`div` 3) arbitrary) arbitrary
    shrink (ValFin f) = ValFin <$> shrink f

instance (Arbitrary d, Arbitrary v) => Arbitrary (Output d v) where
    arbitrary = Output <$> arbitrary <*> arbitrary <*> arbitrary
    shrink (Output p d v) =
           (Output p d <$> shrink v)             -- shrink the validator
        ++ ((\d' -> Output p d' v) <$> shrink d) -- shrink the datum

instance (Arbitrary r, Arbitrary d, Arbitrary v) => Arbitrary (Transaction r d v) where

    arbitrary = Transaction <$> arbitrary <*> arbitrary

    shrink (Transaction is os) =
           (Transaction is <$> shrink os)
        ++ (flip Transaction os <$> shrink is)

instance (Arbitrary r, Arbitrary d, Arbitrary v) => Arbitrary (Context r d v) where
    arbitrary = Transaction <$> arbitrary <*> arbitrary

newtype ValidTx r d v = ValidTx (Transaction r d v) deriving (Show, Generic)

fromValidTx :: ValidTx r d v -> Transaction r d v
fromValidTx (ValidTx tx) = tx

instance (Arbitrary r, Arbitrary d, Arbitrary v) => Arbitrary (ValidTx r d v) where

    arbitrary = do
        tx <- arbitrary
        return $ ValidTx $ go [tx]
      where
        go []                     = Transaction [] []
        go (tx : txs)
            | transactionValid tx = tx
            | otherwise           = go $ take 10 $ txs ++ shrink tx

    shrink (ValidTx tx) = ValidTx <$> shrink tx

instance ( Arbitrary r
         , Support r
         , Arbitrary d
         , Support d
         , Arbitrary v
         , Validator r d v
         ) => Arbitrary (Chunk r d v) where
    arbitrary = sized $ \size -> do
        l <- choose (0, min limit size)
        scale (min limit) $ go l
      where
        go :: Int -> Gen (Chunk r d v)
        go 0    = return pzero
        go l = do
            valids <- replicateM 5 $ scale (min limit) arbitrary
            chunk  <- go $ pred l
            go' valids chunk

        go' [] chunk = return chunk
        go' (ValidTx tx : txs) chunk = do
            let c  = unsafeSingletonChunk tx
            let c1 = padd c chunk
                c2 = padd chunk c
            case (c1, c2) of
                (Just chunk', _)           -> return chunk'
                (Nothing    , Just chunk') -> return chunk'
                (Nothing    , Nothing)     -> go' txs chunk

        limit :: Int
        limit = 15

    shrink = const [] -- TODO: We need something better here

newtype SmallChunk r d v = SmallChunk (Chunk r d v)
    deriving Show

instance Arbitrary (Chunk r d v) => Arbitrary (SmallChunk r d v) where
    arbitrary = SmallChunk <$> scale (min 7) arbitrary
    shrink (SmallChunk ch) = SmallChunk <$> shrink ch

class Validator r d v => Fixable r d v | v -> r d where
    -- | Takes a context and an output and modifies the output such that it can be consumed by the context.
    fixOutput :: Context r d v -> Output d v -> Output d v

instance (Support r, Support d) => Fixable r d (Val r d) where  

    fixOutput (Transaction (Input p _ :| _) _) (Output _ d _) =
        Output p d $ Val $ EvFun $ const True

instance (Eq r, UnifyPerm r, Eq d, UnifyPerm d) => Fixable r d (ValFin r d) where
    fixOutput c@(Transaction (Input p _ :| _) _) (Output _ d (ValFin f)) =
          Output p d (ValFin $ extEvFinMap (d, c) True f) 

instance (Support r, Support d) => Fixable r d (ValTriv r d) where
    fixOutput (Transaction (Input p _ :| _) _) (Output _ d v) = Output p d v


fixChunkToBlockchain :: (Arbitrary d, Arbitrary v, Fixable r d v) 
   => Chunk r d v -> Gen (Blockchain r d v) 
fixChunkToBlockchain chunk 
   | isBlockchain chunk = return $ blockchain chunk
   | otherwise = do -- Gen monad 
       -- get the utxcs of the chunk, still in a Nom binding
       let utxcsCh' = utxcsOfChunk chunk
       -- generate an arbitrary output for each utxc /first/ 
       os' <- replicateM (resAppC length utxcsCh') arbitrary -- :: Gen (Output d v) 
       -- and only /then/ unpack the list of utxcs.  Fresh atoms generated are for input-output bindings and should not interfere with atoms in os' 
       let cs = genUnNom $ utxcsCh' 
       -- fix each output so it matches the relevant utxc.
       let os = map (uncurry fixOutput) (zip cs os')  
       -- make genesis block
       let genesis = unsafeSingletonChunk (Transaction [] os)
       -- add it to the chunk and parcel it up as a blockchain
       -- genesis block is on the right because lists grow from right-to-left in Haskell 
       return . blockchain . fromJust $ chunk `padd` genesis 

instance ( Arbitrary r
         , Support r 
         , Arbitrary d
         , Support d
         , Arbitrary v
         , Fixable r d v
         ) => Arbitrary (Blockchain r d v) where
    arbitrary = arbitrary >>= fixChunkToBlockchain 

    shrink = const [] -- TODO: We need something better here


-- Tests

-- TODO: two ways to combine different validator types in one property, one lightweight, one more heavy-handed:
-- Given prop_chunkrefl below, you can either manually (or in the actual test suite) do
--
-- quickCheck $ prop_chunkrefl atVal
-- quickCheck $ prop_chunkrefl atValFin
--
-- If you want to automate this, you can use the ValProxy-machinery above, so by doing
--
-- quickCheck $ withVal (property . prop_chunkrefl)
--
-- a random validator type will be picked for each test. We could extend this to include more different validator types
-- and also to include types for redeemers and/or datum if we want.

{-- Types 1
type TR = () 
type TD = () 
type TV = ValTriv TR TD 
--}

-- Types 2 
type TR = Int  
type TD = Int   
type TV = ValFin TR TD
--

type TC = Chunk TR TD TV
type SmallTC = SmallChunk TR TD TV
type TB = Blockchain TR TD TV
type TX = ValidTx TR TD TV

type TC' v = Chunk TR TD v

atValTriv :: Proxy (ValTriv TR TD)
atValTriv = Proxy

atValFin :: Proxy (ValFin TR TD)
atValFin = Proxy

type CVal v = (Typeable v, Show v, Arbitrary v, UnifyPerm v, Validator TR TD v)

data ValProxy where
    ValProxy :: CVal v => Proxy v -> ValProxy    

instance Show ValProxy where
    show (ValProxy (Proxy :: Proxy v)) = "{" ++ show (typeRep :: TypeRep v) ++ "}"

instance Arbitrary ValProxy where
    arbitrary = elements [ValProxy atValTriv, ValProxy atValFin]
    shrink = const []

valTriv, valFin :: ValProxy
valTriv = ValProxy atValTriv
valFin = ValProxy atValFin

withVal :: (forall v proxy. CVal v => proxy v -> a) -> ValProxy -> a
withVal f (ValProxy p) = f p

-- | Sanity check: every arbitrary chunk is indeed a valid chunk.
prop_arbitraryChunkIsValid :: TC -> Bool
prop_arbitraryChunkIsValid = isChunk

-- | Sanity check: every arbitrary chunk is indeed a valid chunk (alternate test).
prop_arbitraryChunkIsValid' :: TC -> Bool
prop_arbitraryChunkIsValid' = isChunk'

-- | Sanity check: every arbitrary chunk is equal to itself (not trivial because 'Eq' instance is nontrivial)
prop_arbitraryChunkEqCheck :: TC -> Bool
prop_arbitraryChunkEqCheck ch = ch == ch


-- | Sanity check: not every chunk is a blockchain (might have UTxIs)! 
prop_notEveryChunkBlockchain :: TC -> Property 
prop_notEveryChunkBlockchain c = expectFailure $ isBlockchain c


-- | Sanity check: an arbitrary transaction is indeed a valid transaction.
prop_arbitraryTxIsValid :: TX -> Bool
prop_arbitraryTxIsValid = transactionValid . fromValidTx

-- | Sanity check: an arbitrary blockchain is indeed a valid blockchain.
prop_arbitraryBlockchainIsValid :: TB -> Bool
prop_arbitraryBlockchainIsValid = isBlockchain . getBlockchain


-- | Sanity check: arbitrary instance of TB generates a blockchain, which is equal to itself.
--
-- /'unifiablePerm' must be used here, because of the local scope./ 
prop_blockchainToChunkAndBack :: TB -> Bool
prop_blockchainToChunkAndBack b = (blockchain . getBlockchain $ b) `unifiablePerm` b

-- | Blockchain has no UTxIs
prop_blockchainHasNoUTxIs :: TB -> Bool 
prop_blockchainHasNoUTxIs b = null . utxisOfChunk . getBlockchain $ b

-- | Chunk is equal to itself
prop_chunkrefl :: CVal v => proxy v -> TC' v -> Bool 
prop_chunkrefl _ ch = ch == ch  -- chunk equality goes through @'chunkEq'@

-- | There are two different chunks
prop_chunkneq :: TC -> TC -> Property 
prop_chunkneq ch ch' = expectFailure $ ch == ch'

-- | Empty chunk is prefix of any chunk
prop_emptyIsPrefix :: TC -> Bool
prop_emptyIsPrefix ch = isPrefixChunk (return pzero) ch 

-- | The tail of a chunk, is a chunk.
prop_chunkTail_is_chunk :: TC -> Property 
prop_chunkTail_is_chunk ch = chunkLength ch > 0 ==> isJust $ chunkTail ch

-- | The tail of a chunk, is a prefix of the original chunk.
prop_chunkTail_is_prefix :: TC -> Property 
prop_chunkTail_is_prefix ch = chunkLength ch > 0 ==> isPrefixChunk (fromJust $ chunkTail ch) ch 

-- | The tail of a chunk, generating fresh atoms if required 
genChunkTail :: (UnifyPerm r, UnifyPerm d, UnifyPerm v, Validator r d v) => Chunk r d v -> Maybe (Chunk r d v)
genChunkTail ch = fmap genUnNom $ chunkTail ch

-- | The tail of a chunk, is a prefix of the original chunk.  Gotcha version, that doesn't have the Nom bindings: expect failure here.
prop_chunkTail_is_prefix_gotcha :: TC -> Property 
prop_chunkTail_is_prefix_gotcha ch = expectFailure $ chunkLength ch > 0 ==> isPrefixChunk (return . fromJust $ genChunkTail ch) ch 

-- | Plausible-but-wrong @'warningNotChunkTail'@ is wrong: expect failure here. 
prop_warningNotChunkTail_is_not_chunk :: TC -> Property 
prop_warningNotChunkTail_is_not_chunk ch = expectFailure $ chunkLength ch > 0 ==> fromJust $ isChunk <$> warningNotChunkTail ch
-- prop_warningNotChunkTail_is_not_chunk ch = expectFailure $ chunkLength ch > 0 ==> (isJust . nomTxListToChunk) ((chunkToTxList . fromJust . warningNotChunkTail) ch)

-- | /Underbinding/ is when not enough atoms are bound in a chunk 
prop_underbinding :: TC -> Property
prop_underbinding ch = expectFailure $ isChunk $ ch @@! \_ txs -> Chunk (return txs) 

-- | /Overbinding/ is when too many atoms are bound in a chunk 
prop_overbinding :: TC -> Property
prop_overbinding ch = expectFailure $ isChunk $ restrict (S.toList $ supp ch) ch 

-- | Gotcha: Fails because loss of information from two Nom bindings.
prop_chunkHead_chunkTail_recombine :: TC -> Property
prop_chunkHead_chunkTail_recombine ch = expectFailure $ chunkLength ch > 0 ==> unNom $ do -- Nom monad
   h <- fromJust $ chunkHead ch
   t <- fromJust $ chunkTail ch
   return $ Just ch == appendTxChunk h t

-- | Succeeds because one Nom binding thus no loss of information. 
prop_chunkHdTl_recombine :: TC -> Property
prop_chunkHdTl_recombine ch = chunkLength ch > 0 ==> unNom $ do -- Nom monad
   (tx,ch') <- fromJust $ chunkToHdTl ch
   return $ Just ch == appendTxChunk tx ch' 

{- prop_chunkTailIsPrefix :: TC -> Property 
prop_tailIsPrefix ch = 
    let mt = chunkTail ch
    in isJust mt ==> isPrefixChunk (fromJust mt) ch 
-}
{- prop_tailIsPrefix :: TC -> Property 
prop_tailIsPrefix ch = 
    let mt = chunkTail ch
    in isJust mt ==> unNom $ isPrefixChunk (fromJust mt) ch 
-}

-- | If you reverse the order of transactions in a chunk, it need not be valid
prop_reverseIsNotValid :: TC -> Property 
prop_reverseIsNotValid ch = expectFailure $ isJust (reverseTxsOf ch) 

prop_subchunksValid :: SmallChunk TR TD TV -> Bool 
prop_subchunksValid (SmallChunk ch) = and . unNom $ map (isJust . txListToChunk) <$> (subTxListOf ch) 
-- also subchunk and composition interact

-- | If two transactions are apart, they can be validly combined. 
-- | Corresponds to Lemma 2.14(1) of <https://arxiv.org/pdf/2003.14271.pdf UTxO- vs account-based smart contractblockchain programming paradigms>.
prop_apart_is_valid_tx :: TX -> TX -> Bool 
prop_apart_is_valid_tx vtx1 vtx2 = unNom $ do -- Nom monad
      let [tx1, tx2] = fromValidTx <$> [vtx1, vtx2]
      tx2' <- freshen tx2
      return . isJust $ txListToChunk [tx1, tx2']  

-- | If two chunks are apart, they can be validly combined. 
-- | Extends Lemma 2.14(1) of <https://arxiv.org/pdf/2003.14271.pdf UTxO- vs account-based smart contractblockchain programming paradigms>.
prop_apart_is_valid_ch :: TC -> TC -> Bool 
prop_apart_is_valid_ch ch1 ch2 = unNom $ do -- Nom monad
      ch2' <- freshen ch2
      return . isJust $ (Just ch1) <> (Just ch2')


-- A helper to observe equivalence of chunks
observe :: Maybe TC -> Maybe TC -> Maybe TC -> Bool
observe mch1 mch2 mch3 =
     isJust (mch3 <> mch1) == isJust (mch3 <> mch2) 
   &&
     isJust (mch1 <> mch3) == isJust (mch2 <> mch3) 

-- | If two chunks are apart, they can be validly commuted. 
-- | Extends Lemma 2.14(1) of <https://arxiv.org/pdf/2003.14271.pdf UTxO- vs account-based smart contractblockchain programming paradigms>.
-- We use smaller chunks for speed.
prop_chunk_apart_commutes :: SmallTC -> SmallTC -> SmallTC -> Bool 
prop_chunk_apart_commutes (SmallChunk ch1) (SmallChunk ch2) (SmallChunk ch3) = unNom $ do -- Nom monad
      ch2' <- freshen ch2
      return $ observe ((Just ch1) <> (Just ch2'))
                       ((Just ch2') <> (Just ch1)) 
                       (Just ch3) 

-- | This corresponds to a key result, Lemma 2.14(2) of <https://arxiv.org/pdf/2003.14271.pdf UTxO- vs account-based smart contractblockchain programming paradigms>.
prop_validity_fresh :: TC -> Property
prop_validity_fresh ch = chunkLength ch > 1 ==> unNom $ do -- Nom monad
   (tx1, tx2, ch') <- fromJust $ chunkToHdHdTl ch
   let mch2 = appendTxChunk tx1 ch' 
   return $ (isBlockchain ch && isBlockchain' mch2) <= (tx1 `apart` tx2) 
 

