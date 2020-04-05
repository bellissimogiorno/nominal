module Language.Nominal.Properties.NamesSpec
     where

import Test.QuickCheck

import Language.Nominal.Names 
import Language.Nominal.Nom

-- | @nameLabel (nameOverwriteLabel t n) == t@
prop_namelabel :: Name String -> Maybe String -> Bool
prop_namelabel n t' = t' == nameLabel (nameOverwriteLabel t' n) 

-- | Name equality depends on the atom, not the label
prop_namelabel_eq_irrelevant :: Name String -> Maybe String -> Bool
prop_namelabel_eq_irrelevant n t' = 
   n == nameOverwriteLabel t' n

-- | (n' n).x = x  (we expect this to fail)
prop_singleswap :: Name String -> Name String -> [Name String] -> Property 
prop_singleswap n1 n2 l = 
   expectFailure $ swp n1 n2 l == l

-- | n',n#x => (n' n).x = x.  Test on x a tuple.  
prop_freshswap :: Name String -> Name String -> (Name String, Name String, Name String) -> Property 
prop_freshswap n1 n2 l = 
   isFresh n1 l ==> isFresh n2 l ==> 
      swp n1 n2 l == l

-- | (n' n).(n' n).x = x  
prop_doubleswap :: Name String -> Name String -> [Name String] -> Bool
prop_doubleswap n1 n2 l = 
   swp n1 n2 (swp n1 n2 l) == l


-- | n'',n'#x => (n'' n').(n' n).m = (n'' n).m  
prop_doubleswap_fresh' :: Name String -> Name String -> Name String -> Name String -> Property 
prop_doubleswap_fresh' n n' n'' m = 
   isFresh n' m ==> isFresh n'' m ==> 
      swp' n'' n' (swp' n' n m) === swp' n'' n m


-- | n'#x => (n'' n').(n' n).x = (n'' n).x  
prop_doubleswap_fresh :: Name String -> Name String -> Name String -> [Name String] -> Property 
prop_doubleswap_fresh n n' n'' l = 
   isFresh n' l ==> isFresh n'' l ==> 
      swp n'' n' (swp n' n l) === swp n'' n l

