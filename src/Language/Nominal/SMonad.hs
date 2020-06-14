{-|
Module      : A theory of suspended monoid actions
Description : A theory of suspended monoid actions
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Typeclass and instances for a "suspended" monoid action.  Three examples will be of particular interest:

* Suspend a permutation (@'XSwp' s@).  (This is familiar from the theory of /nominal rewriting/, where swappings suspend on unknowns.)  
* Suspend a binding (@'XRes' s@; we use this to define @'Language.Nominal.Nom.KNom'@).   
* Suspend a capture-avoiding binding (@'Language.Nominal.Nom.KNom' s@).  

Intuitively, 'Language.Nominal.Nom.KNom' is just 'XRes' plus 'Swappable' plus 'IO' (for fresh IDs). 
-}

{-# LANGUAGE ConstraintKinds       
           , DataKinds             
           , DefaultSignatures     
           , DeriveAnyClass
           , DerivingVia           
           , DeriveFunctor
           , DeriveGeneric
           , EmptyCase             
           , FlexibleContexts      
           , FlexibleInstances     
           , FunctionalDependencies 
           , GADTs                 
           , InstanceSigs          
           , KindSignatures 
           , MultiParamTypeClasses 
           , PartialTypeSignatures   
           , ScopedTypeVariables     
           , StandaloneDeriving      
           , TupleSections         
           , TypeOperators         
           , UndecidableInstances 
#-}  

module Language.Nominal.SMonad
    where

import           Control.Monad
import           GHC.Generics     hiding (Prefix) -- avoid clash with Data.Data.Prefix
import           Type.Reflection

import           Language.Nominal.Name
import           Language.Nominal.NameSet
import           Language.Nominal.Utilities

-- | A typeclass for computing under a monoid action.  
--
-- RULES: 
--
-- > exit . enter mempty ==  id
-- > flip >>+ . const    ==  >==     i.e.   a' >>= f = a' >>+ const f
-- > enter mempty        ==  return
--
-- In other words:
--
-- * @+<< . const@ and @enter mempty@ form a monad.
-- * @enter mempty@ followed by @exit@ is a noop. 
class Monoid i => SMonad i m | m -> i where
   (>>+) :: m a -> (i -> a -> m b) -> m b
   -- ^ Move from one suspended environment to another via a function @i -> a -> m b@.
   enter :: i -> a -> m a
   -- ^ Enter the suspended environment, by suspending @i@ on @a@.
   exit  :: m a -> a
   -- ^ Exit the suspended environment, discarding any suspended actions. 
   -- Use 'exitWith' to exit while folding actions into the computation. 

{-- instance SMonad i m => Functor m where
    fmap = liftM
instance SMonad i m => Applicative m where
    pure  = return
    (<*>) = ap
instance SMonad i m => Monad m where
    (>>=) a' cont = a' >>+ const cont
    return = enter mempty 
--}
   
(+<<) :: SMonad i m => (i -> a -> m b) -> m a -> m b
(+<<) = flip (>>+)

-- | An equivalent to 'fmap', with access to the monoid.
imap :: SMonad i m => (i -> a -> b) -> m a -> m b
imap f a' = a' >>+ \i a -> enter mempty $ f i a -- mempty -> i?

-- | An equivalent to '<&>', with access to the monoid.
pami :: SMonad i m => m a -> (i -> a -> b) -> m b
pami = flip imap

-- | Exit the 'SMonad', with a function to fold the monoid into the computation.  So:
--
-- > exit = exitWith (,)
exitWith :: SMonad i m => (i -> a -> b) -> m a -> b
exitWith = exit .: imap  

-- | @flip 'exitWith'@
withExit :: SMonad i m => m a -> (i -> a -> b) -> b
withExit = flip exitWith

-- | An 'SMonad' has an @i@-monoid action
iact :: (Monad m, SMonad i m) => i -> m a -> m a
-- iact i a' = a' >>+ \i' a -> enter (i <> i') a 
iact = join .: enter 


----------------------
-- Deriving via machinery for SMonad
--
-- Usage:
--    deriving (Functor, Applicative, Monad) via ViaSMonad <instance-name>

newtype ViaSMonad m a = ViaSMonad {runViaSMonad :: m a}
instance SMonad i m => Functor (ViaSMonad m) where
    fmap = liftM
instance SMonad i m => Applicative (ViaSMonad m) where
    pure = return
    (<*>) = ap
instance SMonad i m => Monad (ViaSMonad m) where
    return = ViaSMonad . enter mempty
    ViaSMonad fa >>= cont = ViaSMonad $ fa >>+ const (runViaSMonad . cont)
----------------------


-- | A generic type for suspended monoid operations 
data XSuspend i a = Suspend i a 
   deriving (Functor, Applicative, Monad) via ViaSMonad (XSuspend i)
   deriving (Generic, Swappable, Eq, Show)

instance Monoid i => SMonad i (XSuspend i) where
   (>>+)  :: XSuspend i a -> (i -> a -> XSuspend i a') -> XSuspend i a' 
   Suspend i a >>+ g = let (Suspend i' a') = g i a in Suspend (i <> i') a'
   enter :: i -> a -> XSuspend i a
   enter = Suspend 
   exit :: XSuspend i a -> a
   exit (Suspend _ a) = a


-- | A type for suspended swappings
type XSwp s a = XSuspend (KPerm s) a

-- | Exit with a swapping action, if available
getSwp :: (Typeable s, Swappable a) => XSwp s a -> a
getSwp = exitWith perm

-- | A type for suspended restrictions 
type XRes s a = XSuspend [KAtom s] a

-- | Exit with a restriction action, if available
getRes :: KRestrict s a => XRes s a -> a
getRes = exitWith restrict

-- * Transpose an 'SMonad' with other constructors.

-- | Transpose an 'SMonad' with a 'Functor'
-- 
-- /Note: if @m@ is instantiated to @'Language.Nominal.Nom.KNom' s@ then note there is no capture-avoidance here; local bindings are just moved around.  A stronger version (with correspondingly stronger typeclass assumptions) is in 'Language.Nominal.Nom.transposeNomF'./ 
transposeMF :: (Functor f, SMonad i m) => m (f a) -> f (m a)
transposeMF = exitWith $ fmap . enter 

-- | This is just an instance of a more general principle, since @f@ is 'Traversable' and we assume @m@ applicative.
transposeFM :: (Traversable f, Applicative m, SMonad i m) => f (m a) -> m (f a)
transposeFM = sequenceA
