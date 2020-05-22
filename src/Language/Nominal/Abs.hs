{-|
Module      : Abs 
Description : Nominal atoms-abstraction types 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Name-abstraction, nominal style.  This captures the "a." in "λa.ab".  

Examples of practical usage are in "Language.Nominal.Examples.SystemF", e.g. the type and term datatypes 'Language.Nominal.Examples.SystemF.Typ' and 'Language.Nominal.Examples.SystemF.Trm'.
-}

{-# LANGUAGE DataKinds             
           , FlexibleContexts      
           , FlexibleInstances     
           , InstanceSigs          
           , MultiParamTypeClasses 
           , PartialTypeSignatures   
           , PolyKinds             
           , ScopedTypeVariables   
           , TupleSections         
           , UndecidableInstances    -- needed for Num a => Nameless a
           , DerivingStrategies    
           , GeneralizedNewtypeDeriving   
           , DeriveAnyClass        
           , DeriveGeneric         
           , DeriveFunctor          
           , DeriveFoldable          
           , DeriveTraversable     
           , PatternSynonyms
#-}  

module Language.Nominal.Abs 
   ( -- * Name-abstraction
     KAbs -- We don't expose the internals of KAbs.  Use @abst@. 
   , Abs 
-- * Abstractions (basic functions)
   , abst, abst', pattern (:@>), fuse, unfuse, absLabel, conc
-- * The bijection between @'Abs'@ and @'Nom'@
   , absToNom, nomToAbs
-- * Unpacking name-contexts and abstractions
   , absFresh, absFresh', absFuncOut
-- * Tests
   -- $tests 
   )
   where

import           Data.Default
import           Type.Reflection (Typeable)
import           GHC.Generics

import Language.Nominal.Utilities ((.:))
import Language.Nominal.Name 
import Language.Nominal.NameSet 
import Language.Nominal.Nom

-- * Name-abstraction

-- | A datatype for name-abstractions.
--
-- * @KAbs n a@ is a type for abstractions of @a@s by @n@-names, where we intend that @n = KName s t@ for some @s@-atoms (atoms of type @s@) and @t@-labels (labels of type @t@). 
-- 
-- * @Abs t a@ is a type for abstractions of @a@s by @t@-labelled @''Tom'@-atoms. 
--
-- Under the hood an abstraction is just an element of @(n, n -> a)@, but we do not expose this.  What makes the type interesting is its constructor, @'abst' :: KName s t -> a -> KAbs (KName s t) a@, which is the only way to build an abstraction. 
--
-- It's possible to implement @'KAbs'@ using @'Nom'@ — see @'absToNom'@ and @'nomToAbs'@ — but this requires a @'KSwappable'@ typeclass constraint on @a@, which we prefer to avoid so that e.g. @'KAbs'@ can be a @'Functor'@. 
--
data KAbs n a = AbsWrapper { 
   absName :: n,   -- ^ We only care about the name for its label.  For reasons having to do with the Haskell type system, it's convenient to wrap this label up in a "dummy name".  We do not export 'absName' outside this file. 
   conc :: n -> a  -- ^ 'conc' stands for /concretion/.  It /concretes/ an abstraction at a particular name.   
-- Unsafe if the name is not fresh. 
--
-- > (abst a x) `conc` a == x
--
-- > abst a (x `conc` a) == x -- provided a is suitably fresh. 
--
-- > new' $ \a -> abst a (x `conc` a) == x  
   }
   deriving ( Generic
            , Functor
            , KSwappable k -- ^ Spelling out the generic swapping action for clarity, where we write @KA@ for the (internal) constructor for @KAbs@: @kswp n1 n2 (KA n f) = KA (kswp n1 n2 n) (kswp n1 n2 f)@
            )

-- | Abstraction by @'Tom'@-names. 
type Abs t a = KAbs (KName 'Tom t) a


-- * Creating abstractions

-- | Create an abstraction by providing a name and a datum in which that name can be swapped (straight out of the paper; <https://link.springer.com/article/10.1007/s001650200016 publisher> and <http://www.gabbay.org.uk/papers.html#newaas-jv author's> pdfs).
abst :: (Typeable (s :: k), KSwappable k a) => KName s t -> a -> KAbs (KName s t) a
abst nam a = AbsWrapper nam $ \nam' -> kswpN nam' nam a

infixr 0 :@>

-- | The abstraction pattern 
--
-- > n :@> x -> f n x
--
-- is synonymous with 
--
-- > x' -> x' @@! f 
--
-- /Note: ':@>' requires @Typeable@, whereas '@@!' doesn't.  This isn't a bug, it's a feature: ':@>' can also be used as an infix constructor synonym for 'abst', and the 'Typeable' condition comes from there./
pattern (:@>) :: (Typeable (s :: k), KSwappable k a) => KName s t -> a -> KAbs (KName s t) a
pattern n :@> f <- n :@@! f where
    (:@>) = abst
{-# COMPLETE (:@>) #-}   -- This match on an abstraction is complete.
 
-- | A 'Name' is just a pair of a label and an 'Atom'.  This version of 'abst' that takes a label and an atom, instead of a name.
abst' :: (Typeable (s :: k), KSwappable k a) => t -> KAtom s -> a -> KAbs (KName s t) a
abst' = abst .: Name 

-- | Fuse abstractions, taking label of abstracted name from first argument.
-- Should satisfy:
--
-- > fuse (abstr n x) (abstr n y) = abstr n (x, y)
--
fuse :: (KAbs (KName s t) a1, KAbs (KName s t) a2) -> KAbs (KName s t) (a1, a2)
fuse (AbsWrapper n1 f1, AbsWrapper _ f2) = AbsWrapper n1 $ \n -> (f1 n, f2 n)  

-- | Split two abstractions.
-- Should satisfy:
--
-- > unfuse (abstr n (x,y)) = (abstr n x, abstr x y)
--
unfuse :: KAbs (KName s t) (a, b) -> (KAbs (KName s t) a, KAbs (KName s t) b) 
unfuse (AbsWrapper n f) = 
   (AbsWrapper n (fst . f), AbsWrapper n (snd . f)) 


-- | Return the label of an abstraction.
--
-- /Note:/ For reasons having to do with the Haskell type system it's convenient to store this label in the underlying representation of the abstraction, using a "dummy name".  However, we do not export access to this name, we only export access to its label, using 'absLabel'. 
absLabel :: KAbs (KName s t) a -> t
absLabel = nameLabel . absName


-- * Abstraction the binder

-- | Acts on an abstraction @x'@ by unpacking @x'@ as @(n,x)@ for a fresh name @n@, and calculating @f n x@.
instance Binder (KAbs (KName s t) a) (KName s t) a s where
   (@@) :: KAbs (KName s t) a -> (KName s t -> a -> b) -> KNom s b
   (@@) x' f = atFresh (absLabel x') $ \n -> f n $ x' `conc` n


-- | Support of a.x is the support of x minus a
instance (Typeable s, KSupport s a, KSupport s t) => KSupport s (KAbs (KName s t) a) where
   ksupp = resAppC . ksupp   -- Use of 'resAppC' here cleans out the (atom of the) abstracted name.


-- * The bijection between @'Abs'@ and @'Nom'@

-- | Bijection between @Nom@ and @Abs@
absToNom :: KAbs (KName s t) a -> KNom s (KName s t, a)
absToNom = nomApp (,)


-- | Bijection between @Nom@ and @Abs@.
nomToAbs :: (Typeable (s :: k), KSwappable k a) => KNom s (KName s t, a) -> KAbs (KName s t) a
nomToAbs = genAppC $ uncurry abst 



-- * Unpacking name-contexts and abstractions


-- | Abstractions are equal up to fusing their abstracted names. 
instance (Typeable s, Eq t, Eq a) => Eq (KAbs (KName s t) a) where
   AbsWrapper n1 f1 == AbsWrapper n2 f2 = 
      (nameLabel n1 == nameLabel n2) && new (nameLabel n1) (\n -> f1 n == f2 n)  -- note atom ids of @n1@ and @n2@ are discarded. 


-- | We show an abstraction by evaluating the function inside `Abs` on a fresh name (with the default `Nothing` label)
instance (Show t, Show a) => Show (KAbs (KName s t) a) where
   show a' = a' @@! \n a -> show n ++ ". " ++ show a   -- could also use @@. or :@>, but this would introduce a @Typeable s@ typeclass condition.


instance Default t => Applicative (KAbs (KName s t)) where -- use typeclass constraint on t.  all usual labels have defaults
   pure  :: a -> KAbs (KName s t) a
   pure a = AbsWrapper (justALabel def) (const a) 
   (<*>) :: KAbs (KName s t) (a -> b) -> KAbs (KName s t) a -> KAbs (KName s t) b
   (<*>) (AbsWrapper n g) (AbsWrapper _ a) = AbsWrapper n $ \nam -> let nam' = (nam `withLabelOf` n) in g nam' $ a nam' -- must choose one of the two labels
-- TODO: use fuse?

-- | Apply f to a fresh element with label @t@
absFresh :: (Typeable (s :: k), KSwappable k a) => t -> (KName s t -> a) -> KAbs (KName s t) a
absFresh t f = genUnNom . atFresh t $ \m -> abst m (f m)

-- | Apply f to a fresh element with default label 
absFresh' :: (Typeable (s :: k), Default t, KSwappable k a) => (KName s t -> a) -> KAbs (KName s t) a
absFresh' = absFresh def 


-- | Near inverse to applicative distribution.
-- @absFuncIn . absFuncOut = id@ but not necessarily other way around 
absFuncOut :: (Typeable (s :: k), KSwappable k a, Default t) => (KAbs (KName s t) a -> KAbs (KName s t) b) -> KAbs (KName s t) (a -> b)
absFuncOut f = AbsWrapper (justALabel def) $ \nam a -> (f (abst nam a)) `conc` nam
-- absFuncOut f = AbsWrapper (justALabel def) $ \nam a -> conc (f (abst nam a)) nam


{- $tests Property-based tests are in "Language.Nominal.Properties.AbsSpec". -}
