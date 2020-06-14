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
           , ScopedTypeVariables   
           , StandaloneDeriving 
           , TupleSections         
           , UndecidableInstances    -- needed for Num a => Nameless a
           , DerivingStrategies    
           , DerivingVia
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

import Data.Data 
import Data.Default
import GHC.Generics hiding (Prefix) -- avoid clash with Data.Data.Prefix

import Language.Nominal.Utilities ((.:))
import Language.Nominal.Name 
import Language.Nominal.NameSet 
import Language.Nominal.Nom
import Language.Nominal.Binder

-- * Name-abstraction

-- | A datatype for name-abstractions.
--
-- * @KAbs n a@ is a type for abstractions of @a@s by @n@-names, where we intend that @n = KName s t@ for some @s@-atoms (atoms of type @s@) and @t@-labels (labels of type @t@). 
-- 
-- * @Abs t a@ is a type for abstractions of @a@s by @t@-labelled @'Tom'@-atoms. 
--
-- Under the hood an abstraction is just an element of @(n, n -> a)@, but we do not expose this.  What makes the type interesting is its constructor, @'abst' :: KName s t -> a -> KAbs (KName s t) a@, which is the only way to build an abstraction. 
--
-- It's possible to implement @'KAbs'@ using @'Nom'@ — see @'absToNom'@ and @'nomToAbs'@ — but this requires a @'KSwappable'@ typeclass constraint on @a@, which we prefer to avoid so that e.g. @'KAbs'@ can be a @'Functor'@. 
--
data KAbs n a = AbsWrapper { 
   absName :: n,   -- ^ We only care about the name for its label.  For reasons having to do with the Haskell type system, it's convenient to wrap this label up in a "dummy name".  We do not export 'absName' outside this file. 
   absApp :: n -> a  -- ^ A function that /concretes/ an abstraction at a particular name.   
-- Unsafe if the name is not fresh. 
--
-- > (abst a x) `absApp` a == x
--
-- > abst a (x `absApp` a) == x -- provided a is suitably fresh. 
--
-- > new' $ \a -> abst a (x `absApp` a) == x  
   }
   deriving ( Generic
            , Functor
            , Swappable -- ^ Spelling out the generic swapping action for clarity, where we write @KA@ for the (internal) constructor for @KAbs@: @kswp n1 n2 (KA n f) = KA (kswp n1 n2 n) (kswp n1 n2 f)@
            , Typeable
            )
-- | Support of a :@> x is the support of x minus a
deriving via BinderSupp (KAbs (KName s t) a) 
   instance (KSupport s a, KSupport s t) => KSupport s (KAbs (KName s t) a) 


-- | Abstraction by @'Tom'@-names. 
type Abs t a = KAbs (KName Tom t) a

-- * Creating abstractions

-- | Create an abstraction by providing a name and a datum in which that name can be swapped (straight out of the paper; <https://link.springer.com/article/10.1007/s001650200016 publisher> and <http://www.gabbay.org.uk/papers.html#newaas-jv author's> pdfs).
--
-- Instance of '@>', for the case of a nominal abstraction.
abst :: (Typeable s, Swappable t, Swappable a) => KName s t -> a -> KAbs (KName s t) a
abst = (@>) 

-- | The abstraction pattern '(:@>)' is just an instance of '(:@@!)' for 'KAbs'.  Thus, 
--
-- > n :@> x -> f n x
--
-- is synonymous with 
--
-- > x' -> x' @@! f 
--
-- Because '(:@>)' is a concrete instance of '(:@@!)', we can declare it @COMPLETE@.
pattern (:@>) :: (Typeable s, Swappable t, Swappable a) => KName s t -> a -> KAbs (KName s t) a
pattern n :@> a <- n :@@! a where
    (:@>) = (@>) -- Explicitly bidirectional pattern synonym.  https://gitlab.haskell.org/ghc/ghc/-/wikis/pattern-synonyms#explicitly-bidirectional-pattern-synonyms
{-# COMPLETE (:@>) #-}   -- States that this match on an abstraction is complete.
infixr 0 :@> 

-- | A 'Name' is just a pair of a label and an 'Atom'.  This version of 'abst' that takes a label and an atom, instead of a name.
abst' :: (Typeable s, Swappable t, Swappable a) => t -> KAtom s -> a -> KAbs (KName s t) a
abst' = (@>) .: Name 

-- | Fuse abstractions, taking label of abstracted name from first argument.
-- Should satisfy:
--
-- > fuse (n @> x) (n @> y) = n @> (x, y)
--
fuse :: (KAbs (KName s t) a1, KAbs (KName s t) a2) -> KAbs (KName s t) (a1, a2)
fuse (AbsWrapper n1 f1, AbsWrapper _ f2) = AbsWrapper n1 $ \n -> (f1 n, f2 n)  

-- | Split two abstractions.
-- Should satisfy:
--
-- > unfuse (n @> (x,y)) = (n @> x, n @> y)
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
instance (Typeable s, Swappable t, Swappable a) => Binder (KAbs (KName s t) a) (KName s t) a s where
   (@@) :: KAbs (KName s t) a -> (KName s t -> a -> b) -> KNom s b
   (@@) x' f = freshKName (absLabel x') @@ \_ n -> f n $ x' `absApp` n
   (@>) :: KName s t -> a -> KAbs (KName s t) a
   (@>) nam a = AbsWrapper nam $ \nam' -> kswpN nam' nam a

-- | Concretes an abstraction at a particular name.   
-- Unsafe if the name is not fresh. 
--
-- > (abst a x) `conc` a == x
--
-- > abst a (x `conc` a) == x -- provided a is suitably fresh. 
--
-- > new' $ \a -> abst a (x `conc` a) == x  
instance Binder (KAbs n a) n a s => BinderConc (KAbs n a) n a s n where 
   conc = absApp
   
-- * The bijection between @'Abs'@ and @'Nom'@


-- | Bijection between @Nom@ and @Abs@.  Just an instance of 'binderToNom'.
absToNom :: (Typeable s, Swappable t, Swappable a) => KAbs (KName s t) a -> KNom s (KName s t, a)
absToNom = binderToNom 

-- | Bijection between @Nom@ and @Abs@.  Just an instance of 'nomToBinder'.
nomToAbs :: (Typeable s, Swappable t, Swappable a) => KNom s (KName s t, a) -> KAbs (KName s t) a
nomToAbs = nomToBinder 



-- * Unpacking name-contexts and abstractions


-- | Abstractions are equal up to fusing their abstracted names. 
instance (Typeable s, Swappable t, Eq t, Eq a) => Eq (KAbs (KName s t) a) where
   AbsWrapper n1 f1 == AbsWrapper n2 f2 = 
      (nameLabel n1 == nameLabel n2) && new (nameLabel n1) (\n -> f1 n == f2 n)  -- note atom ids of @n1@ and @n2@ are discarded. 


-- | We show an abstraction by evaluating the function inside `Abs` on a fresh name (with the default `Nothing` label)
instance (Typeable s, Swappable t, Swappable a, Show t, Show a) => Show (KAbs (KName s t) a) where
   show a' = a' @@! \n a -> show n ++ ". " ++ show a   -- could also use @@. or :@>, but this would introduce a @Typeable s@ typeclass condition.


instance Default t => Applicative (KAbs (KName s t)) where -- use typeclass constraint on t.  all usual labels have defaults
   pure  :: a -> KAbs (KName s t) a
   pure a = AbsWrapper (justALabel def) (const a) 
   (<*>) :: KAbs (KName s t) (a -> b) -> KAbs (KName s t) a -> KAbs (KName s t) b
   (<*>) (AbsWrapper n g) (AbsWrapper _ a) = AbsWrapper n $ \nam -> let nam' = (nam `withLabelOf` n) in g nam' $ a nam' -- must choose one of the two labels
-- TODO: use fuse?

-- | Apply f to a fresh element with label @t@
absFresh :: (Typeable s, Swappable t, Swappable a) => t -> (KName s t -> a) -> KAbs (KName s t) a
absFresh t f = freshKName t @@! \_ m -> m @> f m  -- It's OK to use '@@!' and release the bound ID, because we know it's bound in the result.
--- absFresh t f = genUnNom . atFresh t $ \m -> m @> f m

-- | Apply f to a fresh element with default label 
absFresh' :: (Typeable s, Swappable t, Swappable a, Default t) => (KName s t -> a) -> KAbs (KName s t) a
absFresh' = absFresh def 


-- | Near inverse to applicative distribution.
-- @absFuncIn . absFuncOut = id@ but not necessarily other way around 
absFuncOut :: (Typeable s, Swappable t, Swappable a, Swappable b, Default t) => (KAbs (KName s t) a -> KAbs (KName s t) b) -> KAbs (KName s t) (a -> b)
absFuncOut f = AbsWrapper (justALabel def) $ \nam a -> f (nam @> a) `conc` nam


{- $tests Property-based tests are in "Language.Nominal.Properties.AbsSpec". -}
