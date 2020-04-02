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

{-# LANGUAGE TemplateHaskell       #-}  -- needed for QuickCheck test generation
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}  -- needed for Num a => Nameless a
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeSynonymInstances  #-}
-- {-# LANGUAGE OverlappingInstances  #-}  
{-# LANGUAGE PartialTypeSignatures #-}  

{-# OPTIONS_GHC -Wno-orphans #-}  -- suppress orphan instance warning for Swappable

module Language.Nominal.Nom
    where

import           Control.Monad
import qualified Data.Map as DM 
import           System.IO.Unsafe (unsafePerformIO)


import Language.Nominal.Names 


-- * The Nom monad (low-level functions)


-- | Data in local name context
newtype Nom t a = Nom (IO ([Name t], a))


-- | Fresh names are generated when name contexts are opened 
instance Eq a => Eq (Nom t a) where
   (Nom laz1) == (Nom laz2) = unsafePerformIO $ do -- IO monad
      (_, a1) <- laz1
      (_, a2) <- laz2
      return $ a1 == a2

-- | 'return' wraps datum in the empty name-context.  
--   '>>=' merges name-contexts, avoiding capture. 
instance Monad (Nom t) where
   return :: a -> Nom t a
   (>>=)  :: Nom t a -> (a -> Nom t b) -> Nom t b
   return a = Nom (return ([], a))  -- Wrap datum in the empty name-context 
   (Nom laz1) >>= g = Nom $ do -- IO monad
      (nams1, a1) <- laz1 
      let Nom laz2 = g a1
      (nams2, a2) <- laz2
      return (nams1 ++ nams2, a2)

instance Functor (Nom t) where
  fmap :: (a -> b) -> Nom t a -> Nom t b
  fmap = liftM
instance Applicative (Nom t) where
  pure :: a -> Nom t a
  (<*>) :: Nom t (a -> b) -> Nom t a -> Nom t b
  pure = return
  (<*>) = ap

-- | Removes a name-binding context, leaving its contents (including any dangling names) intact.  
-- Only use this if you know what you're doing; if in doubt use 'unNom' instead.
unsafeUnNom :: Nom t a -> a
unsafeUnNom (Nom x') = snd $ unsafePerformIO x' 

{-- show :: Nom t a -> String
show x = "Nominal"
--}
{-- | Show a nom by unpacking it
show :: (Show a, Show t) => Nom t a -> String
show (Nom a') = unsafePerformIO $ do -- IO monad
   (l, a) <- a'
   return $ "((" ++ Prelude.show l ++ "))." ++ (Prelude.show a)
--}

-- | Access to a nominal datum-in-context as some fresh names and the datum.  
(@!) :: Nom t a -> ([Name t] -> a -> b) -> b
(@!) (Nom x) f = unsafePerformIO $ do -- IO monad
   (ns, a) <- x
   return $ f ns a 

infixr 9 @!


-- * The Nom monad (higher-level functions)

-- | Create a fresh name-in-nominal-context with label 't''
freshNameNom :: Maybe t -> Nom t (Name t) 
freshNameNom t'' = Nom $ do -- IO monad
   a <- freshNameIO t'' 
   return ([a], a) 


-- | Create a fresh name-in-nominal-context with label 't''
freshName :: t -> Nom t (Name t) 
freshName t = Nom $ do -- IO monad
   a <- freshNameIO (Just t) 
   return ([a], a) 

-- | Create a name-context containing a fresh name, with default 'Nothing' label. 
freshName' :: Nom t (Name t) 
freshName' = Nom $ do -- IO monad
   a <- freshNameIO Nothing
   return ([a], a) 


-- | Basic capture-avoidance device: given a list of names and a datum 'a', generate fresh versions of the names and freshen them in 'a'.  We need swappings to do this. 
freshenNomBody :: Swappable t a => ([Name t], a) -> IO ([Name t], a)
freshenNomBody (nams, a) = do -- IO monad
   nams' <- freshNamesIO nams
   return $ (nams', perm (zip nams' nams) a)

-- | Wraps 'a' in a name-binding context, binding 'names'.
res :: Swappable t a => [Name t] -> a -> Nom t a
res nams a  = Nom $ freshenNomBody (nams, a)

-- | Restrict 'atms' in 'a', inside Nom monad
resM :: Swappable t a => [Name t] -> Nom t a -> Nom t a
resM nams x = x >>= res nams 

-- | atFresh f returns the value of f at a fresh name with label 'Just t'
atFresh :: t -> (Name t -> a) -> Nom t a
atFresh t f = f <$> (freshName t)

-- | atFresh' f returns the value of f at a fresh name with label 'Nothing'
atFresh' :: (Name t -> a) -> Nom t a
atFresh' f = f <$> (freshNameNom Nothing)

-- | Map f to res n. f(n) for fresh n
resF :: (Name t -> Nom t a) -> Nom t a
resF = join . atFresh' 

-- | Check that n is fresh for a, nominal style 
isFresh :: (Eq a, Swappable t a) => Name t -> a -> Bool
isFresh n a = unNom $ do -- Nom monad
   a' <- atFresh' (\n' -> swp n n' a)
   return $ a' == a 

-- * Nameless datatypes 

-- | Elements of these types cannot contain any atoms, and so can be safely 'unNom'ed in all circumstances.  'unNom' removes the name-binding context. 
class Nameless a where
   unNom :: Nom t a -> a  
instance {-# OVERLAPPABLE #-} Num a => Nameless a where 
   unNom = unsafeUnNom  
instance Nameless Char where
   unNom = unsafeUnNom  
instance Nameless Bool where
   unNom = unsafeUnNom 
instance Nameless () where
   unNom = unsafeUnNom 
instance (Nameless a, Nameless b) => Nameless (a,b) where
   unNom = unsafeUnNom 
instance (Nameless a, Nameless b, Nameless c) => Nameless (a,b,c) where
   unNom = unsafeUnNom 
instance Nameless a => Nameless [a] where
   unNom = unsafeUnNom 
instance Nameless a => Nameless (Maybe a) where
   unNom = unsafeUnNom 
instance (Nameless a, Nameless b) => Nameless (a -> b) where
   unNom = unsafeUnNom 
instance (Nameless a, Nameless b) => Nameless (DM.Map a b) where
   unNom = unsafeUnNom 

-- | Swapping names in nameless types is trivial
instance {-# OVERLAPPABLE #-} Nameless a => Swappable t a where
   swp _ _ a = a 

