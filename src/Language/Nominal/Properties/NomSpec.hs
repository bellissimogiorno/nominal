module Language.Nominal.Properties.NomSpec
    where

import Test.QuickCheck

import Language.Nominal.Names 
import Language.Nominal.Nom

-- | Check restriction creates local scope.  
-- Should return False.
prop_split_scope :: Name String -> Bool
prop_split_scope n = unNom $ do -- Nom monad
   let (x1,x2) = (res [n] n, res [n] n) -- create two scopes
   y1 <- x1                             -- unpack them
   y2 <- x2
   return $ y1 /= y2                    -- check for equality

{-- test6 = unNom $ do -- Nom monad
   n <- freshName ()                      -- make a fresh name
   let (x1,x2) = (res [n] n, res [n] n)   -- create two abstractions
   y1 <- x1                               -- unpack them
   y2 <- x2
   return $ y1 == y2                      -- check for equality
--}

-- | n' # n if n' is chosen fresh, after n
prop_fresh_neq :: Name () -> Bool 
prop_fresh_neq n = unNom $ do -- Nom monad
   n' <- freshName ()
   return $ n /= n' 

-- | @freshName () /= freshName ()@  Lazy evaluation means distinct fresh names generated.
prop_fresh_neq' :: Bool 
prop_fresh_neq' = let x = freshName () in x /= x

-- | Same thing using @let@. 
prop_fresh_neq'' :: Bool 
prop_fresh_neq'' = let x = unsafeUnNom (freshName ()) in x == x

-- | But if we unpack a single fresh name monadically, we can compare it for equality.
prop_fresh_eq :: Bool 
prop_fresh_eq = 
   let x' = freshName () in 
   unNom $ do -- Nom monad
      x <- x'
      return $ x == x

-- | @~ (n # (n,n'))@
prop_isFresh1 :: Name () -> Name () -> Bool 
prop_isFresh1 n n' = not $ isFresh n (n,n')

-- | @n # n'@
prop_isFresh2 :: Name () -> Bool 
prop_isFresh2 n = unNom $ do -- Nom monad
   n' <- freshName ()
   return $ isFresh n n'


