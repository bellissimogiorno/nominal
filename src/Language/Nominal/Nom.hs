{-|
Module      : Nom 
Description : Nominal-flavoured implementation of data in a context of local names
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Nominal-flavoured implementation of data in a context of local names
-}

{-# LANGUAGE DataKinds             
           , DeriveFoldable          
           , DeriveFunctor           
           , DeriveGeneric         
           , DeriveTraversable       
           , FlexibleContexts      
           , FlexibleInstances     
           , FunctionalDependencies 
           , InstanceSigs          
           , MultiParamTypeClasses 
           , PartialTypeSignatures   
           , PatternSynonyms
           , PolyKinds             
           , ScopedTypeVariables  
           , TypeApplications 
           , ViewPatterns
#-}  

module Language.Nominal.Nom
   ( -- * The Nom monad (low-level functions)
     KNom, Nom, nomToIO,
     -- * The @'Binder'@ typeclass
     -- $binder
     Binder (..), (@@!), (@@.), pattern (:@@!), nomApp, nomAppC, genApp, genAppC, resApp, resAppC, resAppC',
     -- * Destroying a @'Nom'@
     unNom, genUnNom, nomTo, 
     -- * Creating fresh ids in a @'Nom'@
     freshKAtom, freshAtom, freshKAtoms, freshAtoms, freshKName, freshName, freshKNames, freshNames, atFresh, 
      -- * Creating a @'Nom'@
     res, kres, resN,
     -- * 'Nom' and 'Maybe' 
     transposeNomMaybe, transposeMaybeNom,
     -- * @'new'@ quantifier
     newA, new, new', freshFor,
     -- * @'Nom'@ and @'supp'@
     kfreshen, freshen, 
     -- * Detecting trivial @'KNom'@s, that bind no atoms in their argument
     isTrivialNomBySupp, isTrivialNomByEq
     -- * Tests
     -- $tests
   )
   where

import           Control.Monad
import           Data.Proxy       (Proxy (..))
import           System.IO.Unsafe (unsafePerformIO)
import           Data.Default
import           Data.Functor 
import           Data.Maybe
import           Data.Set         as S (toList)
import           Flow 
import           Type.Reflection  (Typeable)
import           GHC.Generics

import Language.Nominal.Name 
import Language.Nominal.NameSet
import Language.Nominal.Utilities


-- * The Nom monad (low-level functions)

-- | Data in local @s@-atom-binding context
newtype KNom s a = Nom { nomToIO :: IO ([KAtom s], a) -- ^ Recover a name-generating IO action from a 'KNom' binding.  If you execute one of these using 'unsafePerformIO', you get the data in @a@ (the /body/ of the binding), with some actual freshly-generated atoms.  This is what 'genUnNom' does (see also the "safe" version 'unNom'). 
                       }
   deriving (Generic, Functor)

-- | Data in a local atom-binding context at @'Tom'@s.
type Nom a = KNom 'Tom a

-- | A general method to exit a 'KNom' binding.
--
-- The use of 'unsafePerformIO' triggers execution of the IO action, which here just generates fresh unique identifiers for the bound atoms.
--
-- Only use this if you know what you're doing; if in doubt use @'unNom'@ instead.
nomTo :: ([KAtom s] -> a -> b) -> KNom s a -> b
nomTo f = unsafePerformIO . fmap (uncurry f) . nomToIO 

-- | Removes a name-binding context, exposing the body of the abstraction for some choice of fresh atoms.
--
-- The use of 'unsafePerformIO' triggers execution of the IO action, which here just generates fresh unique identifiers for the bound atoms.
--
-- Only use this if you know what you're doing; if in doubt use @'unNom'@ instead.
genUnNom :: KNom s a -> a
genUnNom = nomTo $ const id

-- | Use this to safely exit a @'KNom'@ monad.  
-- It works by binding the @KNom@-bound @s@-atoms using @a@'s native instance of @KRestrict@.  See "Language.Nominal.Examples.Tutorial" for examples. 
--
-- > unNom = resAppC id
unNom :: KRestrict s a => KNom s a -> a
unNom = nomTo restrict


-- * Binder

{- $binder

'Binder' is a typeclass for unpacking local bindings.
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
class Binder ctxbody ctx body s | ctxbody -> ctx, ctxbody -> body, ctxbody -> s  where
   (@@) :: ctxbody           -- ^ the data in its local binding  
       -> (ctx -> body -> b) -- ^ function that inputs an explicit name context @ctx@ and a @body@ for that context, and outputs a @b@. 
       -> KNom s b           -- ^ Result is a @b@ in a binding context.

infixr 9 @@ 

-- | Use this to map a binder to a type @b@, generating fresh atoms for any local bindings, and allowing them to escape.
(@@!) :: Binder ctxbody ctx body s => ctxbody -> (ctx -> body -> b) -> b
(@@!) = genUnNom .: (@@) 
-- (@@!) x' f = genUnNom $ x' @@ f 

infixr 9 @@! 

pattern (:@@!) :: Binder ctxbody ctx body s => ctx -> body -> ctxbody
pattern ctx :@@! body <- ((@@! \ctx' body' -> (ctx', body')) -> (ctx, body))

-- | Acts on a 'KNom' binder by applying a function to the body and the context of locally bound names.  Local names are preserved. 
instance Binder (KNom s a) [KAtom s] a s where
   (@@) :: KNom s a -> ([KAtom s] -> a -> b) -> KNom s b 
   x' @@ f = Nom $ do -- IO monad
      (atms, x) <- nomToIO x' 
      return (atms, f atms x)

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
-- A common type instance is @(a -> Bool) -> KNom s a -> Bool@, in which case 'resAppC' acts to capture-avoidingly apply a predicate under a binder, and return the relevant truth-value.  See for example the code for 'transposeNomMaybe'. 
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

-- * 'Nom' the monad

-- | 'return' wraps datum in the empty name-context.  
--   '>>=' merges name-contexts.  Capture-avoidance is automagical.
instance Monad (KNom s) where
   return :: a -> KNom s a
   (>>=)  :: KNom s a -> (a -> KNom s b) -> KNom s b
   return a = Nom (return ([], a))  -- Wrap datum in the empty name-context 
   (Nom laz1) >>= g = Nom $ do -- IO monad
      (atms1, a1) <- laz1 
      let Nom laz2 = g a1
      (atms2, a2) <- laz2
      return (atms1 ++ atms2, a2)

-- | @pure a = res [] a@
instance Applicative (KNom s) where
  pure :: a -> KNom s a
  (<*>) :: KNom s (a -> b) -> KNom s a -> KNom s b
  pure = return
  (<*>) = ap


-- | Show a nom by unpacking it
instance Show a => Show (KNom s a) where
    show a' = a' @@! \atms a -> show atms ++ "." ++ show a  -- Could also use @@. here, but this would introduce a 'Typeable s' typeclass constraint.  


-- | Swap goes under name-binders.
--
-- > swp n1 n2 (res ns x) = res (swp n1 n2 ns) (swp n1 n2 x) 
instance (Typeable (s :: k), KSwappable k a) => KSwappable k (KNom s a) where
   kswp n1 n2 (Nom a') = Nom $ do -- IO monad
      (atms, a) <- a' 
      return (kswp n1 n2 atms, kswp n1 n2 a) 
-- short, but exits and then re-enters the Nom and IO monads.
-- swp n1 n2 a' = a' @@! \ns a -> res (swp n1 n2 ns) (swp n1 n2 a) 


-- * Creating fresh ids in a @'Nom'@

-- | Create a fresh atom-in-nominal-context 
freshKAtom :: KNom s (KAtom s) 
freshKAtom = Nom $ do -- IO monad
   [a] <- freshKAtomsIO [()] 
   return ([a], a) 

-- | Canonical version for unit atoms sort.
freshAtom :: Nom Atom
freshAtom = freshKAtom

-- | Fresh list of atoms 
freshKAtoms :: [t] -> KNom s [KAtom s]
freshKAtoms = mapM (const freshKAtom) 

-- | Fresh list of atoms (''Tom' instance) 
freshAtoms :: [t] -> Nom [Atom]
freshAtoms = freshKAtoms 

-- | Create a fresh name-in-a-nominal-context with label @t@
freshKName :: t -> KNom s (KName s t) 
freshKName t = freshKAtom <&> Name t

-- | Create fresh names-in-a-nominal-context 
freshKNames :: [t] -> KNom s [KName s t] 
freshKNames = mapM freshKName 

-- | Canonical version for @''Tom'@ type.
freshName :: t -> Nom (Name t)
freshName = freshKName

-- | Canonical version for @''Tom'@ type.
freshNames :: [t] -> Nom [Name t]
freshNames = freshKNames

-- | atFresh f returns the value of f at a fresh name with label @t@
atFresh :: t -> (KName s t -> a) -> KNom s a
atFresh t f = freshKName t <&> f


-- * Creating a @'Nom'@

-- | Basic capture-avoidance device: given a list of names and a datum 'a', generate fresh versions of the atoms and freshen them in 'a'.  
--
-- The effect is to wrap 'a' in a binding context.
-- We need swappings to do this. 
res :: (Typeable (s :: k), KSwappable k a) => [KAtom s] -> a -> KNom s a
res atms a = do -- Nom monad
   atms' <- freshKAtoms atms
   return $ perm (zip atms' atms) a

-- | A version of 'res' that accepts a proxy to explicitly specify the type of atoms.
kres :: (Typeable (s :: k), KSwappable k a) => proxy s -> [KAtom s] -> a -> KNom s a
kres _ = res

-- | Wraps 'a' in a name-binding context, binding 'names'.
resN :: (Typeable (s :: k), KSwappable k a) => [KName s t] -> a -> KNom s a
resN = res . fmap nameAtom 
-- resN ns = res (nameAtom <$> ns)



-- | @'Nom'@ and @'Restrict'@

-- | 'KRestrict' @atms@ in @a@, inside 'KNom' monad.
instance (Typeable (s :: k), KSwappable k a) => KRestrict s (KNom s a) where
   restrict atms x = x >>= res atms 


-- | @supp (res ns x) == supp x \\ ns@
instance (Typeable s, KSupport s a) => KSupport s (KNom s a) where
    ksupp = resAppC . ksupp  -- supp returns a set.  Restriction on a set of atoms coincides with \\ (sets subtraction) 



-- * 'Nom' and 'Maybe' 

-- | Maybe Nom -> Nom Maybe is a fact
transposeNomMaybe :: (Typeable (s :: k), KSwappable k a) => KNom s (Maybe a) -> Maybe (KNom s a)
transposeNomMaybe p = 
   toMaybe (resAppC isJust p)            -- If p has the form res atms Just x 
           (p >>= (fromJust .> return))  -- then res atms Just x --> Just res atms x

-- | Nom Maybe -> Maybe Nom follows by general principles since Maybe is traversable and Nom is applicative (being a Functor), and Traversable has sequenceA 
transposeMaybeNom :: Maybe (Nom a) -> Nom (Maybe a)
transposeMaybeNom = sequenceA



-- * `Nom` and `Eq`

-- | Fresh names are generated when name contexts are opened for equality test 
instance (Typeable s, Eq a) => Eq (KNom s a) where
   a1' == a2' = unNom $ do -- Nom monad
      a1 <- a1'
      a2 <- a2'
      return $ a1 == a2


-- * New quantifier

-- | Evaluate predicate on fresh atom. 
newA :: KRestrict s b => (KAtom s -> b) -> b 
newA = resAppC' freshKAtom 

-- | Evaluate predicate on fresh name with label @t@.
new :: KRestrict s b => t -> (KName s t -> b) -> b 
new = resAppC' . freshKName 
-- new t = nomPred' (freshKName t)
-- new t = unNom . atFresh t

-- | Evaluate predicate on fresh name with default label (if this exists) 
new' :: (Default t, KRestrict s b) => (KName s t -> b) -> b 
new' = new def


-- | @n@ is @'freshFor'@ @a@ when @swp n' n a == a@ for a @'new'@ @n'@.  Straight out of the paper (<https://link.springer.com/article/10.1007/s001650200016 publisher> and <http://www.gabbay.org.uk/papers.html#newaas-jv author's> pdfs).
--
-- /Note: In practice we mostly need this for names, but if you need a version that takes an atom instead, then use @'justAnAtom'@ to force the atom to a name.  This may change./
freshFor :: (Typeable (s :: k), Eq a, KSwappable k a) => KName s t -> a -> Bool 
freshFor n a = new (nameLabel n) $ \n' -> kswpN n' n a == a


-- * @'KNom'@ and @'KSupport'@


-- | Freshen all @s@-atoms, if we have @'KSupport'@.  Returns result inside @'KNom'@ binding to store the freshly-generated atoms. 
kfreshen :: (Typeable (s :: k), KSupport s a, KSwappable k a) => proxy s -> a -> KNom s a    
kfreshen p a = res (S.toList $ ksupp p a) a 

-- | Freshen all atoms, if we have @'Support'@.
freshen :: (Support a, Swappable a) => a -> Nom a  
freshen = kfreshen atTom

-- * Detecting trivial @'KNom'@s, that bind no atoms in their argument

-- | Is the @'Nom'@ binding trivial?  
--
-- This is the @'KSupport'@ version, for highly structured data that we can traverse (think: lists, tuples, sums, and maps). 
--
-- See also @'isTrivialNomByEq'@, for less structured data when we have equality @'Eq'@ and swapping 'KSwappable'. 
isTrivialNomBySupp :: forall k s a. (Typeable (s :: k), KSupport s a) => KNom s a -> Bool
isTrivialNomBySupp = resApp $ kapart (Proxy :: Proxy s) 

-- | Is the @'Nom'@ binding trivial?  
--
-- This is the @'Eq'@ version, using @'freshFor'@.
-- Use this when we /do/ have equality and swapping, but /can't/ (or don't want to) traverse the type (think: sets). 
--
-- See also @'isTrivialNomBySupp'@, for when we have @'KSupport'@.
isTrivialNomByEq :: (Typeable (s :: k), KSwappable k a, Eq a) => KNom s a -> Bool
isTrivialNomByEq = resApp $ \atms a -> and $ (`freshFor` a) <$> (justAnAtom <$> atms) 


{- $tests Property-based tests are in "Language.Nominal.Properties.NomSpec". -}
