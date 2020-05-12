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
#-}  

module Language.Nominal.Abs 
   ( -- * Name-abstraction
     KAbs -- We don't expose the internals of KAbs.  Use @abst@. 
   , Abs 
-- * Creating abstractions
   , abst , abst', fuse , unfuse
-- * Destroying abstractions
   , conc, (@#), (@$), absToRestrict, absLabel
-- * The bijection between @'Abs'@ and @'Nom'@
   , absToNom, nomToAbs
-- * Unpacking name-contexts and abstractions
   , absFresh, absFresh', absFuncOut
-- * Substitution 
   , subM
-- * Tests
   -- $tests 
   )
   where

import           Data.Default
import           Type.Reflection (Typeable)
import           GHC.Generics

import Language.Nominal.Name 
import Language.Nominal.NameSet 
import Language.Nominal.Nom
import Language.Nominal.Sub

-- * Name-abstraction

-- | A typeclass for name-abstractions.
--
-- * @KAbs n a@ is a type for abstractions of @a@s by @n@-names, where we intend that @n = KName s t@ for some @s@-atoms (atoms of type @s@) and @t@-labels (labels of type @t@). 
-- 
-- * @Abs t a@ is a type for abstractions of @a@s by @t@-labelled @''Tom'@-atoms. 
--
-- Under the hood an abstraction is just an element of @(n, n -> a)@, but we do not expose this.  What makes the type interesting is its constructor, @'abst' :: KName s t -> a -> KAbs (KName s t) a@, which is the only way to build an abstraction. 
--
-- It's possible to implement @'KAbs'@ using @'Nom'@ — see @'absToNom'@ and @'nomToAbs'@ — but this requires a @'KSwappable'@ typeclass constraint on @a@, which we prefer to avoid so that e.g. @'KAbs'@ can be a @'Functor'@. 
--
data KAbs n a = KAbsWrapper { absName :: n, absFun :: n -> a }
   deriving ( Generic
            , Functor
            , KSwappable k -- ^ Spelling out the generic swapping action for clarity, where we write @KA@ for the (internal) constructor for @KAbs@: @kswp n1 n2 (KA n f) = KA (kswp n1 n2 n) (kswp n1 n2 f)@
            )

-- | Abstraction by @'Tom'@-names. 
type Abs t a = KAbs (KName 'Tom t) a



-- * Creating abstractions

-- | Create an abstraction by providing a name and a datum in which that name can be swapped (straight out of the paper; <https://link.springer.com/article/10.1007/s001650200016 publisher> and <http://www.gabbay.org.uk/papers.html#newaas-jv author's> pdfs).
abst :: (Typeable (s :: k), KSwappable k a) => KName s t -> a -> KAbs (KName s t) a
abst nam a = KAbsWrapper nam $ \nam' -> kswpN nam' nam a

-- | A 'Name' is just a pair of a label and an 'Atom'.  This version of 'abst' that takes a label and an atom, instead of a name.
abst' :: (Typeable (s :: k), KSwappable k a) => t -> KAtom s -> a -> KAbs (KName s t) a
abst' t atm = abst (Name t atm) 

-- | Fuse abstractions, taking label of abstracted name from first argument.
-- Should satisfy:
--
-- > fuse (abstr n x) (abstr n y) = abstr n (x, y)
--
fuse :: (KAbs (KName s t) a1, KAbs (KName s t) a2) -> KAbs (KName s t) (a1, a2)
fuse (KAbsWrapper n1 f1, KAbsWrapper _ f2) = KAbsWrapper n1 $ \n -> (f1 n, f2 n)  

-- | Split two abstractions.
-- Should satisfy:
--
-- > unfuse (abstr n (x,y)) = (abstr n x, abstr x y)
--
unfuse :: KAbs (KName s t) (a, b) -> (KAbs (KName s t) a, KAbs (KName s t) b) 
unfuse (KAbsWrapper n f) = 
   (KAbsWrapper n (fst . f), KAbsWrapper n (snd . f)) 


-- * Destroying abstractions

-- | Concrete an abstraction at a name.  Unsafe if the name is not fresh for @a@.
--
-- > (abst a x) `conc` a == x
--
-- > abst a (x `conc` a) == x -- provided a is suitably fresh. 
--
-- > new' $ \a -> abst a (x `conc` a) == x  
conc :: KAbs (KName s t) a -> KName s t -> a
conc (KAbsWrapper nam' f) nam = f $ nam `withLabelOf` nam'

-- | Version of concretion '@$' (below) that leaves the fresh name in a 'Nom' binding. 
(@#) :: KAbs (KName s t) a -> (KName s t -> a -> b) -> KNom s b
(@#) (KAbsWrapper n' f') f = atFresh (nameLabel n') $ \n -> f n (f' n)

infixr 9 @#

-- | Concretion.  To destroy an abstraction x', provide it with an f and calculate x' @$ f.
-- This unpacks x' as (n,x) for a fresh name n, and calculates f n x.
(@$) :: KAbs (KName s t) a -> (KName s t -> a -> b) -> b
(@$) x f = unsafeUnNom $ x @# f

infixr 9 @$

-- @$
-- @$$
-- >>@
-- @#
-- @$


-- | Map out of an 'Abs' to a type @b@ with its own notion of atoms-restriction
absToRestrict :: KRestrict s b => KAbs (KName s t) a -> (KName s t -> a -> b) -> b
absToRestrict x' f = unNom $ x' @# f 

-- | Support of a.x is the support of x minus a
instance (Typeable s, KSupport s a, KSupport s t) => KSupport s (KAbs (KName s t) a) where
    ksupp p a' = absToRestrict a' $ const $ ksupp p
--    supp a' = a' @$ \n a -> restrict @s [nameAtom n] $ supp a 
--    supp a' = a' @$ \n a -> restrict @s (S.toList $ supp n) $ supp a 

-- | Return the label of an abstraction
absLabel :: KAbs (KName s t) a -> t
absLabel = nameLabel . absName
-- absLabel a = a @$ \n _ -> nameLabel n


-- * The bijection between @'Abs'@ and @'Nom'@

-- | Bijection between @Nom@ and @Abs@
absToNom :: KAbs (KName s t) a -> KNom s (KName s t, a)
absToNom a' = a' @# (,)


-- | Bijection between @Nom@ and @Abs@.
nomToAbs :: (Typeable (s :: k), KSwappable k a) => KNom s (KName s t, a) -> KAbs (KName s t) a
nomToAbs a' = a' >>$ \_ (n, a) -> abst n a   



-- * Unpacking name-contexts and abstractions


-- | Abstractions are equal up to fusing their abstracted names. 
instance (Typeable s, Eq t, Eq a) => Eq (KAbs (KName s t) a) where
   KAbsWrapper n1 f1 == KAbsWrapper n2 f2 = 
      (nameLabel n1 == nameLabel n2) && new (nameLabel n1) (\n -> f1 n == f2 n)  -- note ids of @n1@ and @n2@ are discarded. 


-- | We show an abstraction by evaluating the function inside `Abs` on a fresh name (with the default `Nothing` label)
instance (Show t, Show a) => Show (KAbs (KName s t) a) where
   show a' = a' @$ \n a -> show n ++ ". " ++ show a


instance Default t => Applicative (KAbs (KName s t)) where -- use typeclass constraint on t.  all usual labels have defaults
   pure  :: a -> KAbs (KName s t) a
   pure a = KAbsWrapper (justALabel def) (const a) 
   (<*>) :: KAbs (KName s t) (a -> b) -> KAbs (KName s t) a -> KAbs (KName s t) b
   (<*>) (KAbsWrapper n g) (KAbsWrapper _ a) = KAbsWrapper n $ \nam -> let nam' = (nam `withLabelOf` n) in g nam' $ a nam' -- must choose one of the two labels

-- | Apply f to a fresh element with label @t@
absFresh :: (Typeable (s :: k), KSwappable k a) => t -> (KName s t -> a) -> KAbs (KName s t) a
absFresh t f = unsafeUnNom . atFresh t $ \m -> abst m (f m)

-- | Apply f to a fresh element with default label 
absFresh' :: (Typeable (s :: k), Default t, KSwappable k a) => (KName s t -> a) -> KAbs (KName s t) a
absFresh' = absFresh def 


-- | Near inverse to applicative distribution.
-- @absFuncIn . absFuncOut = id@ but not necessarily other way around 
absFuncOut :: (Typeable (s :: k), KSwappable k a, Default t) => (KAbs (KName s t) a -> KAbs (KName s t) b) -> KAbs (KName s t) (a -> b)
absFuncOut f = KAbsWrapper (justALabel def) $ \nam a -> conc (f (abst nam a)) nam

-- * Substitution

-- | Nameless form of substitution, where the name for which we substitute is packaged in a @'KAbs'@ abstraction. 
subM :: KSub (KName s n) x y => KAbs (KName s n) y -> x -> y
subM y' x = y' @$ \n y -> sub n x y

-- | sub on a nominal abstraction substitutes in the label, and substitutes capture-avoidingly in the body
instance (Typeable (s :: k), Typeable (u :: k), KSub (KName s n) x t, KSub (KName s n) x y, KSwappable k t, KSwappable k y) => 
            KSub (KName s n) x (KAbs (KName u t) y) where
  sub n x y' = y' @$ \n' y -> abst (sub n x <$> n') $ sub n x y
--  sub n x y' = y' @$ \n' y -> abst (nameOverwriteLabel (sub n x (nameLabel n')) n') $ sub n x y
---   sub n x (KAbsWrapper nam f) = KAbsWrapper (nameOverwriteLabel (sub n x $ nameLabel nam) nam)
---                                 (\n' -> sub n x $ f (n' `withLabelOf` nam)) 
--   sub n x absy = let l = absLabel absy in 
--      Abs (nameOverwriteLabel (sub n x l) n) $ \n' -> sub n x $ absFun absy (nameOverwriteLabel l n') 
--   sub n x (KAbsWrapper nam f) = KAbsWrapper (justALabel (sub n x $ nameLabel nam))
--                                 (\n' -> sub n x $ f (n' `withLabelOf` nam))  
---     sub n x y' = y' @$ \n' y -> abst n' $ sub n x y

{- $tests Property-based tests are in "Language.Nominal.Properties.AbsSpec". -}
