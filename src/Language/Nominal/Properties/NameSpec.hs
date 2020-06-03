module Language.Nominal.Properties.NameSpec
     where

import Test.QuickCheck

import Language.Nominal.Name
-- import Language.Nominal.Nom
import Language.Nominal.Binder

-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Test.QuickCheck
-- >>> import Language.Nominal.Properties.SpecUtilities

-- | @'withLabel'@ does indeed overwrite the label.
--
-- prop> \(n :: Name String) t -> nameLabel (n `withLabel` t) == t
--
prop_namelabel :: Name String -> String -> Bool
prop_namelabel n t = t == nameLabel (n `withLabel` t) 

-- | Not all names are equal (even with trivial labels)
prop_twonames :: Name () -> Name () -> Property 
prop_twonames n1 n2 = 
   expectFailure $ n1 == n2

-- | (n' n).x = x  (we expect this to fail)
prop_singleswap :: Name String -> Name String -> [Name String] -> Property 
prop_singleswap n1 n2 l = 
   expectFailure $ swpN n1 n2 l == l

-- | n',n#x => (n' n).x = x.  Test on x a tuple.
prop_freshswap :: Name String -> Name String -> (Name String, Name String, Name String) -> Property
prop_freshswap n1 n2 l = 
   n1 `freshFor` l ==> n2 `freshFor` l ==> 
      swpN n1 n2 l == l

-- | (n' n).(n' n).x = x  
prop_doubleswap :: Name String -> Name String -> [Name String] -> Bool
prop_doubleswap n1 n2 l = 
   swpN n1 n2 (swpN n1 n2 l) == l

-- | n'',n'#x => (n'' n').(n' n).m = (n'' n).m  
prop_doubleswap_fresh' :: Name String -> Name String -> Name String -> Name String -> Property 
prop_doubleswap_fresh' n n' n'' m = 
   n' `freshFor` m ==> n'' `freshFor` m ==> 
      swpN n'' n' (swpN n' n m) === swpN n'' n m

-- | n'#x => (n'' n').(n' n).x = (n'' n).x  
prop_doubleswap_fresh :: Name String -> Name String -> Name String -> [Name String] -> Property 
prop_doubleswap_fresh n n' n'' l = 
   n' `freshFor` l ==> n'' `freshFor` l ==> 
      swpN n'' n' (swpN n' n l) === swpN n'' n l

-- | (n' n).x = (n n').x
prop_swap_symm :: Name String -> Name String -> [Name String] -> Bool
prop_swap_symm n' n x = swpN n' n x == swpN n n' x

