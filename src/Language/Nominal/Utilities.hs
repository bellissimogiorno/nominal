{-|
Module      : Utilities 
Description : Helper functions 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Helper functions 
-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}  -- needed for Num a => Nameless a
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE PartialTypeSignatures #-}  

module Language.Nominal.Utilities 
    where

import           Data.List
import           Data.Maybe

-- * Utilities

-- | 'mkCong g f x' tries to compute 'f x', but if this returns 'Nothing' then control passes to 'g', which should be a function of two arguments which descends recursively into its second argument 'x' and applies its first argument 'mkCong g f' to the subparts of 'x'.
mkCong :: ((a -> a) -> a -> a) -> (a -> Maybe a) -> a -> a
mkCong g f x = fromMaybe (g (mkCong g f) x) (f x)

class Cong a where
   congRecurse :: (a -> a) -> a -> a
   cong :: (a -> Maybe a) -> a -> a
   cong = mkCong congRecurse


-- | Apply f repeatedly until we reach a fixedpoint
repeatedly :: Eq a => (a -> a) -> a -> a
repeatedly f x = if f x == x then x else repeatedly f (f x)


-- | Apply a list of functions in succession.
chain :: [a -> a] -> a -> a
chain = foldr (.) id
-- https://hackage.haskell.org/package/speculate-0.4.1/docs/src/Test.Speculate.Utils.List.html#chain

-- mjg used?
interleave :: [[a]] -> [a]
interleave = concat . transpose

-- | Standard function, returns @Just a@ provided if @True@, and @Nothing@ otherwise 
toMaybe :: Bool -> a -> Maybe a
toMaybe True  a = Just a
toMaybe False _ = Nothing
 
-- | List subset.  Surely this must be in a library somewhere.
isSubsetOf :: Eq a => [a] -> [a] -> Bool 
isSubsetOf l1 l2 = all (`elem` l2) l1



