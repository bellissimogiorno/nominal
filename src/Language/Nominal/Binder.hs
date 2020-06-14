{-|
Module      : Binder 
Description : Typeclass theory of binders 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Typeclass theory of binders 

-}

{-# LANGUAGE DataKinds
           , DeriveFunctor
           , DeriveGeneric
           , DeriveTraversable
           , DerivingVia
           , FlexibleContexts
           , FlexibleInstances
           , FunctionalDependencies
           , GeneralizedNewtypeDeriving
           , InstanceSigs
           , MultiParamTypeClasses
           , PartialTypeSignatures
           , PatternSynonyms
           , ScopedTypeVariables
           , StandaloneDeriving
           , TypeApplications
           , TypeOperators
           , ViewPatterns
           , UndecidableInstances
#-}

{-# OPTIONS_GHC -fno-warn-orphans #-} -- Suppress orphan instance of Data instance of Binder ctxbody.

module Language.Nominal.Binder
   ( -- * The @'Binder'@ typeclass
     -- $binder
       Binder (..), (@@!), (@@.), pattern (:@@!), nomApp, nomAppC, genApp, genAppC, resApp, resAppC, resAppC'
     -- * @'new'@ quantifier
     , newA, new, freshForA, freshFor
     -- * Detecting trivial @'KNom'@s, that bind no atoms in their argument
     , isTrivialNomBySupp, isTrivialNomByEq
     -- * @'Nom'@ and @'supp'@
     , kfreshen, freshen, BinderSupp (..)
     -- * Binder isomorphism
     -- $binderiso
     , kbinderToNom, knomToBinder, knomToMaybeBinder, binderToNom, nomToBinder, nomToMaybeBinder
     -- * Binder with concretion
     , BinderConc (..)
     -- * Tests
     -- $tests
   )
   where

import Data.Data
import Data.Maybe
import Data.Set         as S (toList) -- , Set) -- , union)
import GHC.Generics     hiding (Prefix) -- avoid clash with Data.Data.Prefix

import Language.Nominal.Utilities
import Language.Nominal.NameSet
import Language.Nominal.Name
import Language.Nominal.Nom


-- * Binder

{- $binder

'Binder' is a typeclass for creating and unpacking local bindings.
The current development contains three instances of 'Binder':

* 'KNom' itself: the primitive binding construct of this package.
* 'Language.Nominal.Abs.KAbs': abstraction by a single name.
* 'Language.Nominal.Examples.IdealisedEUTxO.Chunk': a (generalisation of) EUTxO-style blockchains (the binding is in essence the names of edges connecting input-output pairs).

The simplest way to make a binder is to wrap a 'KNom' in further structure:

* 'Language.Nominal.Examples.IdealisedEUTxO.Chunk' has this design.
Its internal representation is structurally just a 'KNom' (what makes it interesting is that it is wrapped in some smart contructors that validate nontrivial extra structure, involving binding and more).

However, it is possible to design a binder without explicitly mentioning 'KNom' in its underlying representation:

* 'Language.Nominal.Abs.KAbs' is an instance.  For technical reasons its underlying representation uses functions, although a bijection does exist with a 'KNom'-based structure (see 'Language.Nominal.Abs.absToNom' and 'Language.Nominal.Abs.nomToAbs').

What makes 'Binder' interesting is a rich array of destructors (e.g. '@@', '@@!', '@@.', 'nomApp', 'nomAppC', 'genApp', 'genAppC', 'resApp', 'resAppC', 'resAppC'').
These correspond to common patterns of unpacking a binder and mapping to other types, and provide a consistent interface across different binding constructs.

-}

-- | A typeclass for unpacking local binding.
--
-- Provides a function to unpack a binder, giving access to its locally bound names.  Examples of binders include 'KNom', 'Language.Nominal.Abs.KAbs', and 'Language.Nominal.Examples.IdealisedEUTxO.Chunk'.
--
-- A 'Binder' comes with a rich array of destructors, like '@@', '@@!', '@@.', 'nomApp', 'nomAppC', 'genApp', 'genAppC', 'resApp', 'resAppC', 'resAppC''.
-- These correspond to common patterns of unpacking a binder and mapping to other types.
--
-- Below:
--
-- * @ctxbody@ is the type of the datum in its name-binding context, which consists intuitively of data wrapped in a local name binding.  (Canonical example: 'KNom'.)
-- * @ctx@ is the type of a concrete name-carrying representation of the local binding (atom, names, list of atoms, etc).  (Canonical examples: 'KAtom' and @['KAtom']@.)
-- * @body@ is the type of the body of the data.
-- * @s@ is the type of atoms output.  Output will be wrapped in @'KNom' s@.
--
-- For example the 'Language.Nominal.Abs.KAbs' instance of 'Binder' has type @Binder (KAbs (KName s t) a) (KName s t) s a@; and this means that
--
-- * a datum in @ctxbody = KAbs (KName s t) a@ can be unpacked as
-- * something in @ctx = KName s t@ and something in @body = a@, and
-- * mapped by a function of type @KName s t -> a -> b@ using '@@',
-- * to obtain something in @KNom s b@.
--
-- The other destructors ('@@!', '@@.', 'nomApp', 'nomAppC', 'genApp', 'genAppC', 'resApp', 'resAppC', 'resAppC'') are variations on this basic pattern which the wider development shows are empirically useful.
--
-- See also 'kbinderToNom' and 'nomToMaybeBinder'.
class (Typeable s, Swappable ctx, Swappable body, Swappable ctxbody) => Binder ctxbody ctx body s | ctxbody -> ctx body s  where
   -- | A destructor for the binder (required)
   (@@) :: ctxbody           -- ^ the data in its local binding
       -> (ctx -> body -> b) -- ^ function that inputs an explicit name context @ctx@ and a @body@ for that context, and outputs a @b@.
       -> KNom s b           -- ^ Result is a @b@ in a binding context.
   (@>) :: ctx -> body -> ctxbody
   -- ^ A constructor for the binder (optional, since e.g. your instance may impose additional well-formedness constraints on the input).  Call this @res@.
   (@>) = fromJust .: resMay
   -- | A partial constructor for the binder, if preferred.
   resMay :: ctx -> body -> Maybe ctxbody
   resMay = Just .: (@>)
   {-# MINIMAL (@@) #-} -- Please at least provide the destructor (@@).  The constructor is optional, since e.g. your instance may impose additional well-formedness constraints on the input.
infixr 9 @@
infixr 1 @>
-- documentation doesn't appear above for (@>) unless I use -- ^


-- | Use this to map a binder to a type @b@, generating fresh atoms for any local bindings, and allowing them to escape.
(@@!) :: Binder ctxbody ctx body s => ctxbody -> (ctx -> body -> b) -> b
(@@!) = exit .: (@@)
infixr 9 @@!

-- | This pattern is not quite as useful as it could be, because it's too polymorphic to use a COMPLETE pragma on.  You can use it, but you may get incomplete pattern match errors.
pattern (:@@!) :: Binder ctxbody ctx body s => ctx -> body -> ctxbody
pattern ctx :@@! body <- ((@@! (,)) -> (ctx, body))
   where (:@@!) = (@>)
-- {-# COMPLETE (:@@!) #-}   -- States this match is complete.
infixr 0 :@@!

-- | Acts on a 'KNom' binder by applying a function to the body and the context of locally bound names.  Local names are preserved.
instance (Typeable s, Swappable a) => Binder (KNom s a) [KAtom s] a s where
   (@@) :: KNom s a -> ([KAtom s] -> a -> b) -> KNom s b
   (@@) = pami . reRes -- the @reRes@ ensures capture-avoidance, in case the input binding was formed using 'enter' instead of 'res'.
   -- (@@) a' f = imap f $ withExit a' res   -- flip imap 
   (@>) :: (Typeable s, Swappable a) => [KAtom s] -> a -> KNom s a
   (@>) = res

-- | Use this to map a binder to a type @b@ with its own notion of restriction.  Bindings do not escape.
(@@.) :: (Binder ctxbody ctx body s, KRestrict s b) => ctxbody -> (ctx -> body -> b) -> b
(@@.) x' f = unNom $ x' @@ f

infixr 9 @@.



-- | Unpacks a binder and maps into a @'KNom'@ environment.
--
-- 'nomApp' = 'flip' '(@@)'
nomApp :: Binder ctxbody ctx body s => (ctx -> body -> b) -> ctxbody -> KNom s b
nomApp = flip (@@)
-- | Unpacks a binder and maps into a @'KNom'@ environment.
-- Local bindings are not examined, and get carried over to the @'KNom'@.
--
-- 'nomAppC' = 'nomApp' . 'const'
nomAppC :: Binder ctxbody ctx body s => (body -> b) -> ctxbody -> KNom s b
nomAppC = nomApp . const
-- | Unpacks a binder.  New names are generated and released.
--
-- 'genApp' = 'flip' '(@@!)'
genApp :: Binder ctxbody ctx body s => (ctx -> body -> b) -> ctxbody -> b
genApp = flip (@@!)
-- | Unpacks a binder.  New names are generated and released.
-- Local bindings are not examined.
--
-- 'genAppC' = 'genApp' . 'const'
genAppC :: Binder ctxbody ctx body s => (body -> b) -> ctxbody -> b
genAppC = genApp . const
-- | Unpacks a binder and maps to a type with its own @'restrict'@ operation.
--
-- 'resApp' = 'flip' '(@@.)'
resApp :: (Binder ctxbody ctx body s, KRestrict s b) => (ctx -> body -> b) -> ctxbody -> b
resApp = flip (@@.)

-- | Unpacks a binder and maps to a type with its own @'restrict'@ operation.
-- Local bindings are not examined, and get carried over and @'restrict'@ed in the target type.
--
-- A common type instance is @(a -> Bool) -> KNom s a -> Bool@, in which case 'resAppC' acts to capture-avoidingly apply a predicate under a binder, and return the relevant truth-value.  See for example the code for 'transposeNomFunc'.
--
-- 'resAppC' = 'resApp' . 'const'
resAppC :: (Binder ctxbody ctx body s, KRestrict s b) => (body -> b) -> ctxbody -> b
resAppC = resApp . const
-- | Unpacks a binder and maps to a type with its own @'restrict'@ operation.  'Flip'ped version, for convenience.
--
-- A common type instance is @KNom s a -> (a -> Bool) -> Bool @, in which case 'resAppC'' acts to apply a predicate inside a binder and return the relevant truth-value.  See for example the code for 'transposeNomMaybe'.
--
-- 'resAppC'' = 'flip' 'resApp'
resAppC' :: (Binder ctxbody ctx body s, KRestrict s b) => ctxbody -> (body -> b) -> b
resAppC' = flip resAppC


-- * Variants on 'res'


{-- | A version of '@>' (@res@) that accepts a proxy to explicitly specify the type of atoms.
kres :: (Typeable s, Swappable body, Binder ctxbody ctx body s) => proxy s -> ctx -> body -> ctxbody
kres _ = (@>)
--}



-- * New quantifier

-- | Evaluate predicate on fresh atom.
newA :: KRestrict s b => (KAtom s -> b) -> b
newA = resAppC' freshKAtom

-- | Evaluate predicate on fresh name with label @t@.
new :: (KRestrict s b, Swappable t) => t -> (KName s t -> b) -> b
new = resAppC' . freshKName


-- | @n@ is @'freshFor'@ @a@ when @swp n' n a == a@ for a @'new'@ @n'@.  Straight out of the paper (<https://link.springer.com/article/10.1007/s001650200016 publisher> and <http://www.gabbay.org.uk/papers.html#newaas-jv author's> pdfs).
--
-- /Note: In practice we mostly need this for names.  This version is for atoms.
freshForA :: (Typeable s, Swappable a, Eq a) => KAtom s -> a -> Bool
freshForA n a = newA $ \n' -> kswp n' n a == a

-- | @n@ is @'freshFor'@ @a@ when @swp n' n a == a@ for a @'new'@ @n'@.  Straight out of the paper (<https://link.springer.com/article/10.1007/s001650200016 publisher> and <http://www.gabbay.org.uk/papers.html#newaas-jv author's> pdfs).
freshFor :: (Typeable s, Swappable t, Swappable a, Eq a) => KName s t -> a -> Bool
freshFor = freshForA . nameAtom


-- * Detecting trivial @'KNom'@s, that bind no atoms in their argument

-- | Is the @'Nom'@ binding trivial?
--
-- This is the @'KSupport'@ version, for highly structured data that we can traverse (think: lists, tuples, sums, and maps).
--
-- See also @'isTrivialNomByEq'@, for less structured data when we have equality @'Eq'@ and swapping 'KSwappable'.
isTrivialNomBySupp :: forall s a. KSupport s a => KNom s a -> Bool
isTrivialNomBySupp = resApp $ kapart (Proxy :: Proxy s)

-- | Is the @'Nom'@ binding trivial?
--
-- This is the @'Eq'@ version, using @'freshFor'@.
-- Use this when we /do/ have equality and swapping, but /can't/ (or don't want to) traverse the type (think: sets).
--
-- See also @'isTrivialNomBySupp'@, for when we have @'KSupport'@.
isTrivialNomByEq :: (Typeable s, Swappable a, Eq a) => KNom s a -> Bool
isTrivialNomByEq = resApp $ \atms a -> and $ (`freshForA` a) <$> atms


-- * @'KNom'@ and @'KSupport'@


-- | Freshen all @s@-atoms, if we have @'KSupport'@.  Returns result inside @'KNom'@ binding to store the freshly-generated atoms.
kfreshen :: KSupport s a => proxy s -> a -> KNom s a
kfreshen p a = S.toList (ksupp p a) @> a

-- | Freshen all atoms, if we have @'Support'@.
freshen :: Support a => a -> Nom a
freshen = kfreshen atTom

-- | Wrapper for generic method of deriving support of binder
newtype BinderSupp a = BinderSupp {getBinderSupp :: a}
   deriving (Generic, Swappable)

instance (Binder ctxbody ctx body s, KSupport s ctx, KSupport s body) => KSupport s (BinderSupp ctxbody) where
   ksupp p (BinderSupp ctxbody) = ctxbody @@. \ctx body -> ksupp p (ctx, body)  -- Use of '(@@.)' here cleans out bound atoms.

{-- | Standard method to calculate the support of a binder
ksuppBinder :: (Binder ctxbody ctx body s, KSupport s ctx, KSupport s body) => proxy s -> ctxbody -> S.Set (KAtom s)
ksuppBinder = resAppC . ksupp -- Use of 'resAppC' here cleans out the (atom of the) abstracted name.
-- | @supp (ns @> x) == supp x \\ ns@
instance KSupport s a => KSupport s (KNom s a) where
   ksupp = ksuppBinder
--}



-- * Binder isomorphism

{- $binderiso

The 'Binder' class has two functions pointing in opposite directions.
This suggests a standard isomorphism.  We expect:

> binderToNom <$> nomToMaybeBinder x == Just x
> nomToBinder . binderToNom == id

For 'KNom' and 'KAbs' it's safe to use 'knomToBinder'.  For others, like 'Language.Nominal.Examples.IdealisedEUTxO.Chunk', you would need 'knomToMaybeBinder', because additional well-formedness conditions are imposed on the constructor.
-}

kbinderToNom :: Binder ctxbody ctx body s => proxy ctxbody -> ctxbody -> KNom s (ctx, body)
kbinderToNom _ = nomApp (,)

knomToMaybeBinder :: (Typeable s, Swappable ctx, Swappable body, Binder ctxbody ctx body s) => proxy ctxbody -> KNom s (ctx, body) -> Maybe ctxbody
knomToMaybeBinder _ = genAppC $ uncurry resMay

knomToBinder :: (Typeable s, Swappable ctx, Swappable body, Binder ctxbody ctx body s) => proxy ctxbody -> KNom s (ctx, body) -> ctxbody
knomToBinder = fromJust .: knomToMaybeBinder

binderToNom :: Binder ctxbody ctx body s => ctxbody -> KNom s (ctx, body)
binderToNom = kbinderToNom (Proxy :: Proxy ctxbody)

nomToMaybeBinder :: (Typeable s, Swappable ctx, Swappable body, Binder ctxbody ctx body s) => KNom s (ctx, body) -> Maybe ctxbody
nomToMaybeBinder = knomToMaybeBinder (Proxy :: Proxy ctxbody)

nomToBinder :: (Typeable s, Swappable ctx, Swappable body, Binder ctxbody ctx body s) => KNom s (ctx, body) -> ctxbody
nomToBinder = knomToBinder (Proxy :: Proxy ctxbody)

-- * Scrap your boilerplate generic support

binderD :: DataType
binderD = mkDataType "Binder" [binderC]

binderC :: Constr
binderC = mkConstr binderD "(@>)" [] Prefix

instance {-# OVERLAPPABLE #-} (Binder ctxbody ctx body s, Typeable ctxbody, Data ctx, Data body) => Data ctxbody where

    gfoldl k z ctxbody = ctxbody @@! \ctx body -> z (@>) `k` ctx `k` body
    gunfold k z _ = k $ k $ z (@>)
    toConstr   = const binderC
    dataTypeOf = const binderD

-- * Binder with concretion

-- | Sometimes we can /concrete/ a bound entity @ctxbody@ at a datum @a@ (where it need not be the case that @a == ctx@), to return a body @body@.  In the case that @a == ctx@, we expect
--
-- > (a @> x) `conc` a == x
-- > a @> (x' `conc` a) == x
class Binder ctxbody ctx body s => BinderConc ctxbody ctx body s a where
   conc :: ctxbody -> a -> body
   conc = flip cnoc
   cnoc :: a -> ctxbody -> body
   cnoc = flip conc
   {-# MINIMAL conc | cnoc #-}

-- | Suppose we have a nominal abstraction @x' :: KNom s a@ where @a@ has its own internal notion of name restriction.
-- Then @cnoc () x'@ folds the 'KNom'-bound names down into @x'@ to return a concrete element of @a@.
--
-- > cnoc () = unNom
instance (Typeable s, Swappable a, KRestrict s a) => BinderConc (KNom s a) [KAtom s] a s () where
   cnoc = const unNom

-- | Suppose we have a nominal abstraction @x' :: KNom s a@.
-- Then @x' `conc` (Proxy :: Proxy s)@ triggers an IO action to strip the 'KNom' context and concrete @x'@ at some choice of fresh atoms.  
--
-- > cnoc (Proxy :: Proxy s) = exit 
instance (Typeable s, Swappable a) => BinderConc (KNom s a) [KAtom s] a s (Proxy s) where
   cnoc = const exit 

-- | Concrete a nominal abstraction at a particular list of atoms.
-- Dangerous for two reasons:
--
-- * The list needs to be long enough.
-- * There are no guarantees about the order the bound atoms come out in.
instance (Typeable s, Swappable a) => BinderConc (KNom s a) [KAtom s] a s [KAtom s] where
   conc a' st = a' @@! \atms a -> perm (zip st atms) a


{- $tests Property-based tests are in "Language.Nominal.Properties.NomSpec". -}
