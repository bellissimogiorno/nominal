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
           , DeriveFoldable
           , DeriveTraversable
           , DeriveGeneric
           , DerivingVia
           , FlexibleContexts
           , FlexibleInstances
           , FunctionalDependencies
           , GADTs 
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
       KNom (..), Nom
     -- * Creating a @'Nom'@
     , res, kres, resN, reRes 
     -- * Destroying a @'Nom'@
     , unNom -- nomTo, genUnNom, genUnNom', 
     -- * Creating fresh ids in a @'Nom'@
     , freshKAtom, freshAtom, freshKAtoms, freshAtoms, freshKName, freshName, freshKNames, freshNames -- , atFresh
     -- * 'KNom' and other functors
     -- $functor
     , transposeNomF -- transposeTraversableNom  
     -- * Tests
     -- $tests
     , module Language.Nominal.SMonad
   )
   where

-- import Data.Data        hiding (typeRep, TypeRep)
-- import Data.Function    ((&))
-- import Data.Proxy
import Data.Type.Equality
import Type.Reflection
import Control.Applicative  -- for Alternative
import Control.Compose -- for :.
import System.IO.Unsafe (unsafePerformIO)
import Data.Functor
import GHC.Generics     hiding (Prefix) -- avoid clash with Data.Data.Prefix
-- import Flow             ((.>))

import Language.Nominal.Name
import Language.Nominal.NameSet
import Language.Nominal.SMonad
import Language.Nominal.Utilities


-- * The Nom monad

{- $nom

Broadly speaking there are three kinds of functions involving 'KNom':

* 'KNom'-specific functions that may involve creating fresh atoms, but do not involve swappings.
* More general functions involving the 'Language.Nominal.Binder.Binder' typeclass (defined using 'KNom', and of which 'KNom' is the canonical instance).  These functions tend to impose 'Swappable' and 'Typeable' constraints on their type parameters.
* 'KNom'-specific functions in which, for various reasons (elegance, avoiding code duplication, necessity) we make use of both classes of functions above.

This file deals with the first class above.  The second and third are in "Language.Nominal.Binder".

/Remark: 'KNom' is more basic than 'Language.Nominal.Binder.Binder', though it's the canonical instance.  This creates a design tension: is a function on 'KNom' best viewed as a function directly on Nom, or as an instance of a more general function involving Binder?/

-}



-- | Data in local @'KAtom' s@-binding context.
newtype KNom s a = Nom { nomToIO :: IO (XRes s a) -- ^ Recover a name-generating IO action from a 'KNom' binding.  If you execute one of these using 'unsafePerformIO', you get the data in @a@ (the /body/ of the binding), with some actual freshly-generated atoms.  See also 'unNom'.
                       }
   deriving (Generic)
   deriving (Functor, Applicative, Monad) via ViaSMonad (KNom s) 
--   deriving (KSupport s) via BinderSupp (KNom s a) -- avoid forward dependency

-- | Swap goes under name-binders.
--
-- > swp n1 n2 (ns @> x) = (swp n1 n2 ns) @> (swp n1 n2 x)
instance (Typeable s, Swappable a) => Swappable (KNom s a) where
   kswp n1 n2 (Nom x) = Nom $ kswp n1 n2 <$> x

instance SMonad [KAtom s] (KNom s) where
    (>>+)  :: KNom s a -> ([KAtom s] -> a -> KNom s b) -> KNom s b
    (Nom a') >>+ cont = Nom $ do -- IO monad
        a <- a'
        let (atms0, a0) = exitWith (,) a 
        let (Nom b') = cont atms0 a0
        iact atms0 <$> b' 
    -- | Enters a name-binding context. 
    --
    -- /Note: This is a low-level instruction.  It does not enforce capture-avoidance.  Only use it if you know what you're doing; if in doubt use @'res'@ instead, which is higher-level but cost typeclass assumptions)./
    enter :: [KAtom s] -> a -> KNom s a
    enter = Nom . return .: enter 
    -- | Exits a name-binding context, using 'unsafePerformIO'. 
    --
    -- /Note: This is a low-level instruction.  Only use it if you know what you're doing; if in doubt use @'unNom'@ or destructors from "Language.Nominal.Binder" instead, which are higher-level but cost typeclass assumptions./
    --
    -- /Note: This is our only use of 'unsafePerformIO'.  If a fresh ID got generated, then it came from here./
    exit :: KNom s a -> a
    exit = exit . unsafePerformIO . nomToIO 

-- | Data in a local atom-binding context at @'Tom'@s.
type Nom = KNom Tom


instance (KSupport t a, Typeable s) => KSupport t (KNom s a) where
   ksupp p x' = unNom $ ksupp p <$> x' -- use of unNom garbage-collects restricted atoms

-- | 'KRestrict' @atms@ in @a@, inside 'KNom' monad.
instance {-# OVERLAPPING #-} (Typeable s, Swappable a) => KRestrict s (KNom s a) where
   restrict = (=<<) . res 
instance {-# OVERLAPPABLE #-} (Typeable s, Swappable a, KRestrict t a) => KRestrict t (KNom s a) where
   restrict atms x' = case testEquality (typeRep :: (TypeRep t)) (typeRep :: (TypeRep s)) of
-- are s and t the same type?  (this should never trigger, because it should be captured by overlapping instance)
            Just Refl   -> x' >>= res atms 
-- are s and t different types?
            Nothing     -> restrict atms <$> x'

-- | Alternatives are composed in a capture-avoiding manner
instance Alternative f => Alternative ((KNom s) :. f) where
   empty = O $ return empty
   a' <|> b' = O $ do -- Nom monad
      a <- unO a'
      b <- unO b'
      return $ a <|> b



-- * Creating a 'KNom'

-- | Constructor for @'KNom' s@. 
res :: (Typeable s, Swappable a) => [KAtom s] -> a -> KNom s a
res atms a = freshKAtoms atms <&> \atms' -> perm (zip atms' atms) a 

-- | Constructor for @'KNom' s@ (proxy version). 
kres :: (Typeable s, Swappable a) => proxy s -> [KAtom s] -> a -> KNom s a
kres _ = res

-- | Make sure restricted atoms will alpha-convert to avoid capture, if e.g. they were created using 'enter' and not 'res'. 
reRes :: (Typeable s, Swappable a) => KNom s a -> KNom s a
reRes = exitWith res 

-- | A version of 'res' on 'Nom' that takes names, not atoms (it just strips the labels of the names and acts on their atoms).
resN :: (Typeable s, Swappable a) => [KName s t] -> a -> KNom s a
resN = res . fmap nameAtom



-- | Use this to safely exit a @'KNom'@ monad.
-- It works by binding the @KNom@-bound @s@-atoms using @a@'s native instance of @KRestrict@.  See "Language.Nominal.Examples.Tutorial" for examples.
--
-- > unNom = resAppC id
--
-- /Note: The less versions of 'unNom' are the 'exit' and 'exitWith' instances of 'KNom' as an instance of 'SMonad'.  See also 'Language.Nominal.Binder.@@'./ 
unNom :: KRestrict s a => KNom s a -> a
unNom = exitWith restrict



-- * Creating fresh ids in a @'Nom'@

-- | Create a fresh atom-in-nominal-context
freshKAtom :: Typeable s => KNom s (KAtom s)
freshKAtom = Nom $ do -- IO monad
   [a] <- freshKAtomsIO [()]
   return $ enter [a] a

-- | Canonical version for unit atoms sort.
freshAtom :: Nom Atom
freshAtom = freshKAtom

-- | Fresh @'Traversable' m@ of atoms (e.g. @m@ is list or stream)
freshKAtoms :: (Traversable m, Typeable s) => m t -> KNom s (m (KAtom s))
freshKAtoms = mapM (const freshKAtom)

-- | Fresh @'Traversable' m@ of atoms (e.g. @m@ is list or stream).
-- | 'Tom' instance.
freshAtoms :: Traversable m => m t -> Nom (m Atom)
freshAtoms = freshKAtoms

-- | Create a fresh name-in-a-nominal-context with label @t@
freshKName :: Typeable s => t -> KNom s (KName s t)
freshKName t = freshKAtom <&> Name t

-- | Create fresh names-in-a-nominal-context
freshKNames :: (Traversable m, Typeable s) => m t -> KNom s (m (KName s t))
freshKNames = mapM freshKName

-- | Canonical version of 'freshKName' for @'Tom'@ name.
freshName :: t -> Nom (Name t)
freshName = freshKName

-- | Canonical version of 'freshKNames' for @'Tom'@ names.
freshNames :: Traversable m => m t -> Nom (m (Name t))
freshNames = freshKNames

{-- 
-- | atFresh f returns the value of f at a fresh name with label @t@
atFresh :: Typeable s => t -> (KName s t -> a) -> KNom s a
atFresh t f = freshKName t <&> f
--}

-- * 'KNom' and functors

{- $functor

There are three functions that will commute 'KNom' with some other 'f':

* 'transposeNomF'
* 'transposeMF'
* 'transposeFM'

Taken together, these functions are making a point that 'KNom' is compatible with your favourite container type.  Because 'KNom' can commuted, there is no need to wonder whether (for example) a graph-with-binding should be a graph with binding on the vertices, or on the edges, or on the graph overall, or any combination.  All of these are valid design decisions and one may be more /convenient/ than the other, but in the end we can isomorphically commute to a single top-level 'KNom' binding.

In that sense, 'KNom' captures a general theory of binding.
It is also a mathematical justification for why the 'Language.Nominal.Binder.Binder' typeclass turns out to be so useful.

-}


-- | 'KNom' commutes down through functors.
--
-- 'transposeNomF' is a version of 'transposeMF' where bindings are have added capture-avoidance (for inverse, see 'transposeFM'). 
transposeNomF :: (Functor f, Typeable s, Swappable a) => KNom s (f a) -> f (KNom s a)
transposeNomF = exitWith $ fmap . res 
-- transposeNomFunc = exitWith $ fmap . enter 


-- * `Nom` and `Eq`

-- | Fresh names are generated when name contexts are opened for equality test
instance Eq a => Eq (KNom s a) where
   a1' == a2' = exit $ a1' >>= \a1 -> a2' >>= \a2 -> return $ a1 == a2
-- Rendering using 'Binder' machinery is possible, but adds forward dependencies and imposes typeclass condition:
-- instance (Typeable s, Swappable a, Eq a) => Eq (KNom s a) where
--   a1' == a2' = a1' @@. \_ a1 -> a2' @@. \_ a2 -> a1 == a2

-- | Show a nom by unpacking it
instance Show a => Show (KNom s a) where
    show = exitWith $ \atms a -> show atms ++ "." ++ show a


{- $tests Property-based tests are in "Language.Nominal.Properties.NomSpec". -}
