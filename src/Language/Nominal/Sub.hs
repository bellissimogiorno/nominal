{-|
Module      : Sub 
Description : Nominal treatment of substitution
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Nominal treatment of substitution
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

module Language.Nominal.Sub 
    where


import Language.Nominal.Names 
import Language.Nominal.Nom
import Language.Nominal.Abs


-- * Substitution

-- | @sub n x y@ and @subM n.x y@ correspond to 'y[n->x]'.  
class Swappable n y => Sub n x y where
   sub  :: Name n -> x -> y -> y
   sub n x y = subM (absByName n y) x
   subM :: Abs n y -> x -> y
   subM y' x = y' @@ \n y -> sub n x y

-- | sub on names
instance Sub n (Name n) (Name n) where
   sub n n' a = if a == n then n' else a
-- instance Sub n (Name n) (Name n) where
--   subM (Abs f) n = f n

-- | sub on name-contexts 
instance Swappable n a => Sub n a (Name n -> a) where
   sub n x k = \n' -> if n' == n then x else k n'

-- | sub on tuples 
instance (Sub n x a, Sub n x b) => Sub n x (a,b) where
   sub n x (a,b) = (sub n x a, sub n x b)
instance (Sub n x a, Sub n x b, Sub n x c) => Sub n x (a,b,c) where
   sub n x (a,b,c) = (sub n x a, sub n x b, sub n x c)

-- | sub on lists 
instance Sub n x a => Sub n x [a] where
   sub n x a' = sub n x <$> a'

-- | sub on Maybe 
instance Sub n x a => Sub n x (Maybe a) where
   sub n x a' = sub n x <$> a'

-- | sub on nameless type is trivial
instance {-# OVERLAPPABLE #-} Nameless a => Sub n x a where
   sub _ _ a = a

{-- Substitution on an abstraction substitutes in the label and capture-avoidingly in the body
instance (Swappable n y, Sub n x t, Sub n x y) => Sub n x (Abs t y) where
   sub n x y' = (y', sub n x) @@@
                  \a y -> absByName a (sub n x y) -}
-- mjg swp overlap here

-- | sub on a nominal abstraction substitutes in the label, and substitutes capture-avoidingly in the body
instance (Sub n x t, Sub n x y, Swappable n (Name t)) => Sub n x (Abs t y) where
   sub n x (Abs (t', f)) = Abs (sub n x <$> t', \yname -> sub n x $ f (nameOverwriteLabel t' yname))






