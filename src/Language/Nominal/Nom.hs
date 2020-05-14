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
           , InstanceSigs          
           , MultiParamTypeClasses 
           , PartialTypeSignatures   
           , PolyKinds             
           , ScopedTypeVariables   
#-}  

module Language.Nominal.Nom
   ( -- * The Nom monad (low-level functions)
     KNom, Nom, nomToIO,
     -- * Destroying a @'Nom'@
     (>>$), unsafeUnNom, unsafeUnNom', 
     -- * Creating fresh ids in a @'Nom'@
     freshKAtom, freshAtom, freshKAtoms, freshKName, freshName, freshKNames, freshNames, atFresh, 
      -- * Creating a @'Nom'@
     res, kres, resN,
     -- | @'Nom'@ and @'Restrict'@
     (>>#), nomToRestrict, nomPred, nomPred', unNom, 
     -- * 'Nom' and 'Maybe' 
     transposeNomMaybe, transposeMaybeNom,
     -- * @'new'@ quantifier
     new, new', freshFor,
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
import           Data.List.Extra  (disjoint)
import           Flow 
import           Type.Reflection  (Typeable)
import           GHC.Generics

import Language.Nominal.Name 
import Language.Nominal.NameSet


-- * The Nom monad (low-level functions)


-- | Data in local @s@-atom-binding context
newtype KNom s a = Nom { nomToIO :: IO ([KAtom s], a) }
   deriving (Generic, Functor)

-- | Data in a local atom-binding context at @'Tom'@s.
type Nom a = KNom 'Tom a

-- * Destroying a @'Nom'@

-- | Access to a nominal datum-in-context as some fresh names and the datum.  
-- The use of unsafePerformIO triggers execution of the IO action.
-- The IO action just generates fresh unique identifiers for the bound atoms.
-- 
-- The @$@ indicates that fresh atoms can escape scope.  Contrast with @'>>#'@, where fresh atoms remain bound.
(>>$) :: KNom s a -> ([KAtom s] -> a -> b) -> b
(>>$) x' f = unsafePerformIO $ (uncurry f) <$> nomToIO x' -- apply f inside the IO monad, then strip the IO.
{- (>>$) x' f = unsafePerformIO $ do -- IO monad
   (atms, a) <- nomToIO x' -- Generate fresh ids for the bound atoms
   return $ f atms a       -- Feed this into f and return the result.
-}

infixr 9 >>$


-- | Removes a name-binding context, leaving its contents (including any dangling names) intact.  
-- Only use this if you know what you're doing; if in doubt use @'unNom'@ instead.
unsafeUnNom :: KNom s a -> a
unsafeUnNom x' = x' >>$ \_ x -> x

-- | Generate fresh atoms in the binding and release the pair of fresh atoms and body for those atoms.
-- Only use this if you know what you're doing. 
unsafeUnNom' :: KNom s a -> ([KAtom s], a)
unsafeUnNom' x' = x' >>$ (,)


-- | @pure a = res [] a@
instance Applicative (KNom s) where
  pure :: a -> KNom s a
  (<*>) :: KNom s (a -> b) -> KNom s a -> KNom s b
  pure = return
  (<*>) = ap

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


-- | Show a nom by unpacking it
instance Show a => Show (KNom s a) where
    show a' = a' >>$ \atms a -> show atms ++ "." ++ show a


-- | Swap goes under name-binders.
--
-- > swp n1 n2 (res ns x) = res (swp n1 n2 ns) (swp n1 n2 x) 
instance (Typeable (s :: k), KSwappable k a) => KSwappable k (KNom s a) where
   kswp n1 n2 (Nom a') = Nom $ do -- IO monad
      (atms, a) <- a' 
      return (kswp n1 n2 atms, kswp n1 n2 a) 
-- short, but exits and then re-enters the Nom and IO monads.
-- swp n1 n2 a' = a' >>$ \ns a -> res (swp n1 n2 ns) (swp n1 n2 a) 


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
freshKAtoms :: [KAtom s] -> KNom s [KAtom s]
freshKAtoms = mapM (const freshKAtom) 

-- | Create a fresh name-in-a-nominal-context with label @t@
freshKName :: t -> KNom s (KName s t) 
freshKName t = freshKAtom <&> Name t

-- | Create fresh names-in-a-nominal-context 
freshKNames :: [t] -> KNom s [KName s t] 
freshKNames = mapM freshKName 

-- | Canonical version for @''Tom'@ sort.
freshName :: t -> Nom (Name t)
freshName = freshKName

-- | Canonical version for @''Tom'@ sort.
freshNames :: [t] -> Nom [Name t]
freshNames = freshKNames

-- | atFresh f returns the value of f at a fresh name with label @t@
atFresh :: t -> (KName s t -> a) -> KNom s a
atFresh t f = freshKName t <&> f
-- atFresh t f = f <$> freshKName t


-- * Creating a @'Nom'@

-- | Basic capture-avoidance device: given a list of names and a datum 'a', generate fresh versions of the atoms and freshen them in 'a'.  
--
-- The effect is to wrap 'a' in a binding context.
-- We need swappings to do this. 
res :: (Typeable (s :: k), KSwappable k a) => [KAtom s] -> a -> KNom s a
res atms a = do -- Nom monad
   atms' <- freshKAtoms atms
   return $ perm (zip atms' atms) a

kres :: (Typeable (s :: k), KSwappable k a) => proxy s -> [KAtom s] -> a -> KNom s a
kres _ = res

-- | Wraps 'a' in a name-binding context, binding 'names'.
resN :: (Typeable (s :: k), KSwappable k a) => [KName s t] -> a -> KNom s a
resN ns = res (nameAtom <$> ns)



-- | @'Nom'@ and @'Restrict'@

-- | Restrict 'atms' in 'a', inside Nom monad.
instance (Typeable (s :: k), KSwappable k a) => KRestrict s (KNom s a) where
   restrict atms x = x >>= res atms 

-- | Map out of a 'Nom' to a type @b@ which has its own notion of restriction.  The @#@ indicates that no atoms can escape scope.  Contrast with @'>>$'@, where fresh atoms could be released.
(>>#) :: KRestrict s b => KNom s a -> ([KAtom s] -> a -> b) -> b
(>>#) x' f = x' >>$ \ns a -> restrict ns (f ns a) 

infixr 9 >># 

-- | Map out of a 'Nom' to a type @b@ which has its own notion of restriction
nomToRestrict :: KRestrict s b => ([KAtom s] -> a -> b) -> KNom s a -> b
nomToRestrict = flip (>>#)


-- | Canonical instance here is for result type `Bool`, whence the "Pred" (for "predicate").
nomPred :: KRestrict s b => (a -> b) -> KNom s a -> b 
nomPred = nomToRestrict . const 

-- | 'flip'ped version of @'nomPred'@, for convenience
nomPred' :: KRestrict s b => KNom s a -> (a -> b) -> b 
nomPred' = flip nomPred

-- | Use this to exit a @'KNom'@ monad.  
-- It works by binding the @Nom@-bound atoms in the type @a@, assuming that this type supports a notion of restriction @KRestrict@.  See "Language.Nominal.Examples.Tutorial" for examples. 
--
-- >>> unNom = nomPred id
unNom :: KRestrict s a => KNom s a -> a
unNom = nomPred id

-- | @supp (res ns x) == supp x \\ ns@
instance (Typeable s, KSupport s a) => KSupport s (KNom s a) where
    ksupp = nomPred . ksupp  -- supp returns a set.  Restriction on a set of atoms coincides with \\ (sets subtraction) 



-- * 'Nom' and 'Maybe' 

-- | Maybe Nom -> Nom Maybe is a fact
transposeNomMaybe :: (Typeable (s :: k), KSwappable k a) => KNom s (Maybe a) -> Maybe (KNom s a)
transposeNomMaybe p = if nomPred isNothing p -- If p = res atms Nothing
   then Nothing                              -- then nothing
   else Just $ p >>= (fromJust .> return)    -- else res atms Just x --> Just res atms x

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

-- | Evaluate predicate on fresh name with label @t@.
-- This is a canonical use of 'unNom', since 'Bool' is nameless.
new :: KRestrict s b => t -> (KName s t -> b) -> b 
new t = unNom . atFresh t

-- | Evaluate predicate on fresh name with default label (if this exists) 
new' :: (Default t, KRestrict s b) => (KName s t -> b) -> b 
new' = new def


-- | @n@ is @'freshForN'@ @a@ when @swp n' n a == a@ for a @'new'@ @n'@.  Straight out of the paper (<https://link.springer.com/article/10.1007/s001650200016 publisher> and <http://www.gabbay.org.uk/papers.html#newaas-jv author's> pdfs).
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
-- This is the @'KSupport'@ version, for when can traverse the type (think: lists, tuples, and sums). 
--
-- See also @'isTrivialNomByEq'@, for when all we have is an equality @'Eq'@.
isTrivialNomBySupp :: (Typeable (s :: k), KSupport s a) => KNom s a -> Bool
isTrivialNomBySupp a' = a' >>$ \atms a -> atms `disjoint` S.toList (ksupp Proxy a) 

-- | Is the @'Nom'@ binding trivial?  
--
-- This is the @'Eq'@ version, using @'freshFor'@.
-- Use this when we /do/ have an equality but /can't/ necessarily traverse the type (think: sets). 
--
-- See also @'isTrivialNomBySupp'@, for when we have @'KSupport'@.
isTrivialNomByEq :: (Typeable (s :: k), KSwappable k a, Eq a) => KNom s a -> Bool
isTrivialNomByEq a' = a' >>$ \atms a -> and $ (`freshFor` a) <$> (justAnAtom <$> atms) 

{- $tests Property-based tests are in "Language.Nominal.Properties.NomSpec". -}
