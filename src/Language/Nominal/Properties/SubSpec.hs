{-|
Module      : SubSpect 
Description : Substitution properties 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Duplicating some tests from "Language.Nominal.Properties.Examples.SystemFSpec", which has good inductive datatypes to substitute on. 
-}

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds        #-}

module Language.Nominal.Properties.SubSpec
    where

import Test.QuickCheck
import Type.Reflection                   (Typeable)

import Language.Nominal.Name 
import Language.Nominal.Binder
import Language.Nominal.Sub
import Language.Nominal.Abs
import Language.Nominal.Examples.SystemF


-- | y[n-> var n] = y
iprop_sub_id :: (KSub ntyp x y, Eq y) => (ntyp -> x) -> ntyp -> y -> Bool 
iprop_sub_id f n y = y == sub n (f n) y
prop_sub_id_typevar' :: NTyp -> Typ -> Bool 
prop_sub_id_typevar' = iprop_sub_id TVar 
prop_sub_id_termvar :: NTrm -> Trm -> Bool 
prop_sub_id_termvar = iprop_sub_id Var
prop_sub_id_typevar :: NTyp -> Trm -> Bool 
prop_sub_id_typevar = iprop_sub_id TVar

-- | n # y => y[n->x] = y
iprop_sub_fresh :: (Typeable s, Swappable y, Swappable n, KSub (KName s n) x y, Eq y, Show y) => KName s n -> x -> y -> Property 
iprop_sub_fresh n x y = n `freshFor` y ==> (y === sub n x y)
prop_sub_fresh_typevar' :: NTyp -> Typ -> Typ -> Property 
prop_sub_fresh_typevar' = iprop_sub_fresh 
prop_sub_fresh_typevar :: NTyp -> Typ -> Trm -> Property 
prop_sub_fresh_typevar = iprop_sub_fresh 
prop_sub_fresh_termvar :: NTrm -> Trm -> Trm -> Property 
prop_sub_fresh_termvar = iprop_sub_fresh 

-- | n' # y => y[n->n'] = (n' n).y
iprop_sub_perm :: (Typeable s, Swappable y, Swappable n, KSub (KName s n) x y, Eq y, Show y) => (KName s n -> x) -> KName s n -> KName s n -> y -> Property 
iprop_sub_perm f n n' y = n' `freshFor` y ==> sub n (f n') y === kswpN n' n y
prop_sub_perm_typevar' :: NTyp -> NTyp -> Typ -> Property 
prop_sub_perm_typevar' = iprop_sub_perm TVar 
-- this one trapped an error
prop_sub_perm_typevar'' :: NTyp -> NTyp -> Trm -> Property 
prop_sub_perm_typevar'' = iprop_sub_perm TVar 
prop_sub_perm_termvar :: NTrm -> NTrm -> Trm -> Property 
prop_sub_perm_termvar = iprop_sub_perm Var 

-- Test capture-avoidance

-- [n1][n1 -> n2] = n2
prop_sub_singleton1 :: Name Int -> Name Int -> Bool
prop_sub_singleton1 n1 n2 = sub n1 n2 [n1] == [n2]

-- [n2][n1 -> n2] = n2
prop_sub_singleton2 :: Name Int -> Name Int -> Bool
prop_sub_singleton2 n1 n2 = (sub n1 n2 [n2]) == [n2]

 
-- n#n1,n2 ==> (n.x)[n1 -> n2] = n.(x[n1 -> n2])
prop_sub_abs_1 :: Name () -> Name () -> Name () -> [Name ()] -> Property 
prop_sub_abs_1 n n1 n2 x = n /= n1 && n /= n2 ==> (sub n1 n2 (abst n x)) == abst n (sub n1 n2 x)

-- (n.x)[n1 -> n2] = n.(x[n1 -> n2]) fails in general
prop_sub_abs_1' :: Name () -> Name () -> Name () -> [Name ()] -> Property 
prop_sub_abs_1' n n1 n2 x = expectFailure $ (sub n1 n2 (abst n (n:n1:n2:x))) == abst n (sub n1 n2 (n:n1:n2:x))

-- (n.x)[n -> n2] = n.x 
prop_sub_abs_3 :: Name () -> Name () -> [Name ()] -> Bool
prop_sub_abs_3 n n2 x = (sub n n2 (abst n x)) == abst n x
