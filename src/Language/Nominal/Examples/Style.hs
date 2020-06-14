{-|
Module      : Comments on style
Description : Examples of coding style
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Commented examples of coding style.  (Or: ways to abuse this code.) 

-}

{-# LANGUAGE InstanceSigs
           , DeriveGeneric
           , LambdaCase
           , MultiParamTypeClasses
           , DeriveAnyClass       -- to derive 'Swappable'
           , DeriveDataTypeable   -- to derive 'Data'
           , FlexibleInstances
#-}


module Language.Nominal.Examples.Style
    ( 
     -- $intro
     bad_countBinding, bad_countOrder, badRestrict, okRestrict, badEq
    )
    where

-- import Data.Function    ((&))

import Language.Nominal.Name
import Language.Nominal.Nom
import Language.Nominal.Binder

{- $intro
It's tempting to try to provide static guarantees of good behaviour with respect to name-handling.
However, this is expensive and may be impossible: sometimes what makes code good or bad depends on how the output is used.

For example: a substitution of a term for a bound name may involve generating a fresh identifier for that name.
This is reasonable, because we expect the choice of name to be destroyed by the substitution.
We can rewrite the code to avoid this name-generation, at some expense, and arguably this stilts the coding style, but either way it is not clear how a type system can provide a comprehensive answer.

Here, we give examples of programs (that may even still work, but) are arguably ugly. 
So: this file is devoted to some programs that you might think twice about writing.
 
-}

-- | You probably shouldn't count the atoms bound in a 'Nom'.   
--
-- > bad_countBinding :: Swappable a => Nom a -> Int
-- > bad_countBinding x' = x' @@! \atms _ -> length atms
bad_countBinding :: Swappable a => Nom a -> Int
bad_countBinding x' = x' @@! \atms _ -> length atms

-- | You probably shouldn't look at the order of the atoms bound in a 'Nom'.
--
-- > bad_countOrder :: Swappable a => Nom a -> Bool
-- > bad_countOrder x' = x' @@! \atms _ -> isSorted atms
bad_countOrder :: Swappable a => Nom a -> Bool
bad_countOrder x' = x' @@! \atms _ -> isSorted atms

-- | It's OK to create fresh IDs for bound atoms, but doing so /unnecessarily/ is deprecated.
--
-- For example, here is code for a restrict instance of Nom (code simplified for clarity):
--
-- > restrict :: Swappable a => [Atom] -> Nom a -> Nom a
-- > restrict atms x' = x' >>= \x -> res atms x
--
-- We can simplify it down to this:
--
-- > restrict = (=<<) . res 
--
-- The code for 'badRestrict' below does the same thing, but unnecessarily unpacks the local binding, generates fresh IDs for its atoms, and then rebinds.
--
-- > badRestrict :: Swappable a => [Atom] -> Nom a -> Nom a
-- > badRestrict atms' a' = a' @@! \atms a -> res (atms' ++ atms) a
badRestrict :: Swappable a => [Atom] -> Nom a -> Nom a
badRestrict atms' a' = a' @@! \atms a -> res (atms' ++ atms) a

-- | Contrast 'badRestrict' with the similar 'okRestrict'.  What separates them is the use of '(@@!)' instead of '(@@.)' (respectively).  
-- The latter '(@@.)' avoids an intermediate generation of explicit fresh IDs for the bound atoms, and so is better.
--
-- In fact 'okRestrict' is equivalent to the actual 'restrict' instance; it's just expressed using higher-level tools.
--
-- > okRestrict :: Swappable a => [Atom] -> Nom a -> Nom a
-- > okRestrict atms a' = a' @@. \_ -> res atms
--
-- Also OK:
--
-- > okRestrict' atms' = join . fmap (res atms')
okRestrict :: Swappable a => [Atom] -> Nom a -> Nom a
okRestrict atms a' = a' @@. \_ -> res atms


-- | Still on the theme of trying to be parsimonious with generating atoms here is code for an equality instance of 'KNom':
-- 
-- > instance Eq a => Eq (KNom s a) where
-- >    a1' == a2' = exit $ a1' >>= \a1 -> a2' >>= \a2 -> return $ a1 == a2
--
-- Note how we 'exit' at 'Bool'.
-- Contrast with the deprecated version, in which we exit earlier than required, and furthermore, we exit twice (code simplified for clarity):
--
-- > badEq :: Eq a => Nom a -> Nom a -> Bool
-- > badEq a1' a2' = withExit a1' $ \_ a1 -> withExit a2' $ \_ a2 -> a1 == a2
badEq :: Eq a => Nom a -> Nom a -> Bool
badEq a1' a2' = withExit a1' $ \_ a1 -> withExit a2' $ \_ a2 -> a1 == a2







-- from Data.List.Ordered

-- |  The 'isSorted' predicate returns 'True' if the elements of a list occur
-- in non-descending order,  equivalent to @'isSortedBy' ('<=')@.
isSorted :: Ord a => [a] -> Bool
isSorted = isSortedBy (<=)

-- |  The 'isSortedBy' function returns 'True' iff the predicate returns true
-- for all adjacent pairs of elements in the list.
isSortedBy :: (a -> a -> Bool) -> [a] -> Bool
isSortedBy lte = loop
  where
    loop []       = True
    loop [_]      = True
    loop (x:y:zs) = (x `lte` y) && loop (y:zs)

{-- TODO: ksupp p x' = unNom $ ksupp p <$> x'
   -- ksupp p x' = withExit x' $ \atms x -> restrict atms (ksupp p x)
--}
