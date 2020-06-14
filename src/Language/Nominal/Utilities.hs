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

{-# LANGUAGE FlexibleInstances     
           , InstanceSigs          
           , MultiParamTypeClasses 
           , FlexibleContexts      
           , TupleSections         
           , PartialTypeSignatures
#-}  

module Language.Nominal.Utilities 
    where

import           Data.Foldable      (Foldable (..)) -- for toList
import           Data.Generics
import           Data.List
import           Data.List.NonEmpty (NonEmpty (..))
import           GHC.Stack          (HasCallStack)
import           Control.Monad      (guard) 


rewrite :: (Typeable a, Data b) => (a -> Maybe a) -> b -> b
rewrite f b = case cast b of
    Just a
        | Just (Just a') <- cast $ f a -> a'
    _                                  -> gmapT (rewrite f) b

-- | Apply f repeatedly until we reach a fixedpoint
repeatedly :: Eq a => (a -> a) -> a -> a
repeatedly f x = let fx = f x in if fx == x then x else repeatedly f fx

-- | Apply a list of functions in succession.
chain :: [a -> a] -> a -> a
chain = foldr (.) id
-- https://hackage.haskell.org/package/speculate-0.4.1/docs/src/Test.Speculate.Utils.List.html#chain

-- | Standard function, returns @Just a@ provided @True@, and @Nothing@ otherwise 
toMaybe :: Bool -> a -> Maybe a
toMaybe b a = guard b >> return a

-- | List subset.  Surely this must be in a library somewhere.
isSubsetOf :: Eq a => [a] -> [a] -> Bool 
isSubsetOf l1 l2 = all (`elem` l2) l1

-- | Interleave a list of lists to a list
interleave :: [[a]] -> [a]
interleave = concat . transpose

-- | Returns 'Just' the tail of a list if it can, and 'Nothing' otherwise.
safeTail :: [a] -> Maybe [a]
safeTail (_ : xs) = Just xs
safeTail _        = Nothing

-- | Returns 'Just' the head of a list if it can, and 'Nothing' otherwise.
safeHead :: [a] -> Maybe a
safeHead (h : _) = Just h 
safeHead _       = Nothing

-- https://hackage.haskell.org/package/intro-0.7.0.0/docs/Intro.html#v:.:
-- | Compose functions with one argument with function with two arguments.
--
--   @f .: g = \\x y -> f (g x y)@.
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) = (.) . (.)
infixr 8 .:
{-# INLINE (.:) #-}

-- | Finds the unique element in a collection satisfying a predicate. 
-- Results in an error if there is no such element or if there are more than one.
--
-- >>> iota (== 1) [1, 2, 3]
-- 1
--
-- >>> iota (> 1) [1, 2, 3]
-- *** Exception: iota: expected exactly one element to satisfy the predicate, but found at least two
-- ...
--
-- >>> iota (> 3) [1, 2, 3]
-- *** Exception: iota: expected exactly one element to satisfy the predicate, but found none
-- ...
--
iota :: (HasCallStack, Foldable f) => (a -> Bool) -> f a -> a
iota p xs = case filter p $ toList xs of
    [x]     -> x
    []      -> error "iota: expected exactly one element to satisfy the predicate, but found none"
    (_ : _) -> error "iota: expected exactly one element to satisfy the predicate, but found at least two"

-- | point moves the (first) element satisfying the predicate to the head of the list.
-- Error raised if no such element found.
--
-- >>> point even [1,2,3]
-- 2 :| [1,3]
--
-- >>> point even [1,3,5]
-- *** Exception: point: no such element
-- ...
--
point :: Foldable f => (a -> Bool) -> f a -> NonEmpty a
point p = go . toList
  where
    go (x : xs)
        | p x       = x :| xs
        | otherwise = let (y :| ys) = go xs in y :| x : ys
    go []           = error "point: no such element"
