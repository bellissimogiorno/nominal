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

{-# LANGUAGE ConstraintKinds       
           , DataKinds
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
           , TypeFamilies
           , TypeOperators
           , ViewPatterns
           , UndecidableInstances
#-}  

{-# OPTIONS_GHC -fno-warn-orphans #-} -- Suppress orphan instance of Data instance of Binder ctxbody.

module Language.Nominal.Nom
   ( -- * The Nom monad
     -- $nom
       KNom (..), Nom -- nomToIO
     -- * Destroying a @'Nom'@
     , res, genUnNom', genUnNom, nomTo, unNom
     -- * Creating fresh ids in a @'Nom'@
     , freshKAtom, freshAtom, freshKAtoms, freshAtoms, freshKName, freshName, freshKNames, freshNames, atFresh
     -- * 'Nom' and 'Maybe'
     , transposeNomMaybe, transposeMaybeNom, 
     -- * Tests
     -- $tests
   )
   where

-- import Data.Data        hiding (typeRep, TypeRep) 
import Data.Function    ((&))
import Data.Type.Equality
import Type.Reflection
import Control.Monad
import Control.Applicative  -- for Alternative
import Control.Compose -- for :.
import System.IO.Unsafe (unsafePerformIO)
import Data.Functor
import Data.Maybe
import GHC.Generics     hiding (Prefix) -- avoid clash with Data.Data.Prefix
import Flow             ((.>))

import Language.Nominal.Name
import Language.Nominal.NameSet
import Language.Nominal.Utilities


-- * The Nom monad

{- $nom

Broadly speaking there are three kinds of functions involving 'KNom':

* 'KNom'-specific functions that may involve creating fresh atoms, but do not involve swappings.
* More general functions involving the 'Binder' typeclass (defined using 'KNom', and of which 'KNom' is the canonical instance).  These functions tend to impose 'Swappable' and 'Typeable' constraints on their type parameters.
* 'KNom'-specific functions in which, for various reasons (elegance, avoiding code duplication, necessity) we make use of both classes of functions above.

This file deals with the first class above.  The second and third are in "Language.Nominal.Binder".

/Remark: 'KNom' is more basic than Binder, though it's the canonical instance.  This creates a design tension: is a function on 'KNom' best viewed as a function directly on Nom, or as an instance of a more general function involving Binder?  Sometimes the decision is not entirely clear./

-}

-- | Data in local @'KAtom' s@-binding context.
newtype KNom s a = Nom { nomToIO :: IO ([KAtom s], a) -- ^ Recover a name-generating IO action from a 'KNom' binding.  If you execute one of these using 'unsafePerformIO', you get the data in @a@ (the /body/ of the binding), with some actual freshly-generated atoms.  This is what 'genUnNom' does (see also the "safe" version 'unNom').
                       }
   deriving (Generic, Functor) 
--   deriving (KSupport s) via BinderSupp (KNom s a) -- avoid forward dependency

-- | Data in a local atom-binding context at @'Tom'@s.
type Nom = KNom Tom


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
--   x1' >>= g = x1' @@. \_ x1 -> g x1 -- Looks plausible but begs the question because requires @KRestrict s b@

instance Applicative (KNom s) where
  pure :: a -> KNom s a
  (<*>) :: KNom s (a -> b) -> KNom s a -> KNom s b
  pure = return
  (<*>) = ap


instance (KSupport t a, Typeable s) => KSupport t (KNom s a) where
   ksupp p x' = unNom $ ksupp p <$> x'
   -- ksupp p x' = (genUnNom' x') & \(atms, x) -> restrict atms (ksupp p x) 

-- | 'KRestrict' @atms@ in @a@, inside 'KNom' monad.
instance {-# OVERLAPPING #-} (Typeable s, Swappable a) => KRestrict s (KNom s a) where
   restrict atms x' = x' >>= \x -> res atms x 
instance {-# OVERLAPPABLE #-} (Typeable s, Swappable a, KRestrict t a) => KRestrict t (KNom s a) where
   restrict atms x' = case testEquality (typeRep :: (TypeRep t)) (typeRep :: (TypeRep s)) of  
-- are s and t the same type?  (this should never trigger, because it should be captured by overlapping instance)
            Just Refl   -> x' >>= \x -> res atms x 
-- are s and t different types?
            Nothing     -> restrict atms <$> x' 


-- | Alternatives are composed in a capture-avoiding manner
instance Alternative f => Alternative ((KNom s) :. f) where
   empty = O $ return empty
   a' <|> b' = O $ do -- Nom monad
      a <- unO a'
      b <- unO b'
      return $ a <|> b

-- | Swap goes under name-binders.
--
-- > swp n1 n2 (ns @> x) = (swp n1 n2 ns) @> (swp n1 n2 x)
instance (Typeable s, Swappable a) => Swappable (KNom s a) where
   kswp n1 n2 = fmap $ kswp n1 n2

-- | A general method to exit a 'KNom' binding.
--
-- The (single) use of 'unsafePerformIO' triggers execution of the IO action, which here just generates fresh unique identifiers for the bound atoms.
--
-- Only use this if you know what you're doing; if in doubt use @'unNom'@ instead.
--
-- __Note: This is our only use of 'unsafePerformIO'.  If a fresh ID got generated, then it came from here.__
nomTo :: ([KAtom s] -> a -> b) -> KNom s a -> b
nomTo f = unsafePerformIO . fmap (uncurry f) . nomToIO

-- | Low-level constructor for 'KNom'.  Inverse to 'genUnNom''.  Contrast with the higher-level (and more polymorphic) 'kres'.
res :: [KAtom s] -> a -> KNom s a
res l a = Nom $ return (l, a)

-- | Removes a name-binding context, exposing some choice of fresh atoms and the body of the abstraction for that choice.
--
-- For @a' :: 'KNom' s a@ we expect the following to be equivalent:
--
-- > (genUnNom' a') & \(atms, a) -> f atms a
-- > a' @@! f
--
-- However '@@!' goes through the 'Binder' typeclass and therefore imposes typeclass constraints that 'genUnNom'' does not.
genUnNom' :: KNom s a -> ([KAtom s], a)
genUnNom' = nomTo $ (,)

-- | Removes a name-binding context, exposing the body of the abstraction for some choice of fresh atoms.
genUnNom :: KNom s a -> a
genUnNom = snd . genUnNom' 


-- | Use this to safely exit a @'KNom'@ monad.
-- It works by binding the @KNom@-bound @s@-atoms using @a@'s native instance of @KRestrict@.  See "Language.Nominal.Examples.Tutorial" for examples.
--
-- > unNom = resAppC id
unNom :: KRestrict s a => KNom s a -> a
unNom = nomTo restrict

-- * Creating fresh ids in a @'Nom'@

-- | Create a fresh atom-in-nominal-context
freshKAtom :: KNom s (KAtom s)
freshKAtom = Nom $ do -- IO monad
   [a] <- freshKAtomsIO [()]
   return ([a], a)

-- | Canonical version for unit atoms sort.
freshAtom :: Nom Atom
freshAtom = freshKAtom

-- | Fresh @'Traversable' m@ of atoms (e.g. @m@ is list or stream)
freshKAtoms :: Traversable m => m t -> KNom s (m (KAtom s))
freshKAtoms = mapM (const freshKAtom)

-- | Fresh @'Traversable' m@ of atoms (e.g. @m@ is list or stream).
-- | 'Tom' instance.
freshAtoms :: Traversable m => m t -> Nom (m Atom)
freshAtoms = freshKAtoms

-- | Create a fresh name-in-a-nominal-context with label @t@
freshKName :: t -> KNom s (KName s t)
freshKName t = freshKAtom <&> Name t

-- | Create fresh names-in-a-nominal-context
freshKNames :: Traversable m => m t -> KNom s (m (KName s t))
freshKNames = mapM freshKName

-- | Canonical version of 'freshKName' for @'Tom'@ name.
freshName :: t -> Nom (Name t)
freshName = freshKName

-- | Canonical version of 'freshKNames' for @'Tom'@ names.
freshNames :: Traversable m => m t -> Nom (m (Name t))
freshNames = freshKNames

-- | atFresh f returns the value of f at a fresh name with label @t@
atFresh :: t -> (KName s t -> a) -> KNom s a
atFresh t f = freshKName t <&> f


-- * 'Nom' and 'Maybe'


-- | Maybe Nom -> Nom Maybe is a fact
transposeNomMaybe :: (Typeable s, Swappable a) => KNom s (Maybe a) -> Maybe (KNom s a)
transposeNomMaybe p =
   toMaybe (isJust (genUnNom p))         -- If p has the form atms @> Just x (fresh atoms are created to check this, but then discarded)
           (p >>= (fromJust .> return))  -- then atms @> Just x --> Just atms @> x

-- | Nom Maybe -> Maybe Nom follows by general principles since Maybe is traversable and Nom is applicative (being a Functor), and Traversable has sequenceA
transposeMaybeNom :: Maybe (Nom a) -> Nom (Maybe a)
transposeMaybeNom = sequenceA


-- * `Nom` and `Eq`

-- | Fresh names are generated when name contexts are opened for equality test
instance Eq a => Eq (KNom s a) where
   a1' == a2' = genUnNom $ a1' >>= \a1 -> a2' >>= \a2 -> return $ a1 == a2 
-- This is wrong because no guarantee names generated by local bindings are distinct
-- instance Eq a => Eq (KNom s a) where
--   a1' == a2' = (genUnNom' a1') & \(_, a1) -> (genUnNom' a2') & \(_, a2) -> a1 == a2
-- Rendering using 'Binder' machinery is possible, but adds forward dependencies and imposes typeclass condition:
-- instance (Typeable s, Swappable a, Eq a) => Eq (KNom s a) where
--   a1' == a2' = a1' @@. \_ a1 -> a2' @@. \_ a2 -> a1 == a2

-- | Show a nom by unpacking it
instance Show a => Show (KNom s a) where
    show a' = (genUnNom' a') & \(atms, a) -> show atms ++ "." ++ show a


{- $tests Property-based tests are in "Language.Nominal.Properties.NomSpec". -}
