{-|
Module      : SubSpect 
Description : Substitution properties 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Duplicating tests from "Language.Nominal.Properties.Examples.SystemFSpec", which has good inductive datatypes to substitute on. 
-}
module Language.Nominal.Properties.SubSpec
    where

import Test.QuickCheck

import Language.Nominal.Names 
import Language.Nominal.Nom
import Language.Nominal.Sub
import Language.Nominal.Examples.SystemF


-- | y[n-> var n] = y
iprop_sub_id :: (Sub n x y, Eq y) => (Name n -> x) -> Name n -> y -> Bool 
iprop_sub_id f n y = y == sub n (f n) y
prop_sub_id_typevar' :: Name NTyp -> Typ -> Bool 
prop_sub_id_typevar' = iprop_sub_id TVar 
prop_sub_id_termvar :: Name NTrm -> Trm -> Bool 
prop_sub_id_termvar = iprop_sub_id Var
prop_sub_id_typevar :: Name NTyp -> Trm -> Bool 
prop_sub_id_typevar = iprop_sub_id TVar

-- | n # y => y[n->x] = y
iprop_sub_fresh :: (Sub n x y, Eq y, Show y) => Name n -> x -> y -> Property 
iprop_sub_fresh n x y = isFresh n y ==> (y === sub n x y)
prop_sub_fresh_typevar' :: Name NTyp -> Typ -> Typ -> Property 
prop_sub_fresh_typevar' = iprop_sub_fresh 
prop_sub_fresh_typevar :: Name NTyp -> Typ -> Trm -> Property 
prop_sub_fresh_typevar = iprop_sub_fresh 
prop_sub_fresh_termvar :: Name NTrm -> Trm -> Trm -> Property 
prop_sub_fresh_termvar = iprop_sub_fresh 

-- | n' # y => y[n->n'] = (n' n).y
iprop_sub_perm :: (Sub n x y, Eq y, Show y) => (Name n -> x) -> Name n -> Name n -> y -> Property 
iprop_sub_perm f n n' y = isFresh n' y ==> sub n (f n') y === swp n' n y
prop_sub_perm_typevar' :: Name NTyp -> Name NTyp -> Typ -> Property 
prop_sub_perm_typevar' = iprop_sub_perm TVar 
-- this one trapped an error
prop_sub_perm_typevar'' :: Name NTyp -> Name NTyp -> Trm -> Property 
prop_sub_perm_typevar'' = iprop_sub_perm TVar 
prop_sub_perm_termvar :: Name NTrm -> Name NTrm -> Trm -> Property 
prop_sub_perm_termvar = iprop_sub_perm Var 

