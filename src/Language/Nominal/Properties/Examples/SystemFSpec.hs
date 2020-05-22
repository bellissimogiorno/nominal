{-| 
__Please read the source code to view the tests.__
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Language.Nominal.Properties.Examples.SystemFSpec
    where

import Data.Maybe
import Test.QuickCheck
import Type.Reflection                   (Typeable)

import Language.Nominal.Name 
import Language.Nominal.Nom
import Language.Nominal.Sub
import Language.Nominal.Examples.SystemF

-- * Substitution

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
iprop_sub_fresh :: (Typeable (s :: k), KSwappable k y, KSub (KName s n) x y, Eq y, Show y) => KName s n -> x -> y -> Property 
iprop_sub_fresh n x y = n `freshFor` y ==> (y === sub n x y)
prop_sub_fresh_typevar' :: NTyp -> Typ -> Typ -> Property 
prop_sub_fresh_typevar' = iprop_sub_fresh 
prop_sub_fresh_typevar :: NTyp -> Typ -> Trm -> Property 
prop_sub_fresh_typevar = iprop_sub_fresh 
prop_sub_fresh_termvar :: NTrm -> Trm -> Trm -> Property 
prop_sub_fresh_termvar = iprop_sub_fresh 

-- | n' # y => y[n->n'] = (n' n).y
iprop_sub_perm :: (Typeable (s :: k), KSwappable k y, KSub (KName s n) x y, Eq y, Show y) => (KName s n -> x) -> KName s n -> KName s n -> y -> Property 
iprop_sub_perm f n n' y = 
   n' `freshFor` y ==> sub n (f n') y === kswpN n' n y
prop_sub_perm_typevar' :: NTyp -> NTyp -> Typ -> Property 
prop_sub_perm_typevar' = iprop_sub_perm TVar 
-- this one trapped an error
prop_sub_perm_typevar'' :: NTyp -> NTyp -> Trm -> Property 
prop_sub_perm_typevar'' = iprop_sub_perm TVar 
prop_sub_perm_termvar :: NTrm -> NTrm -> Trm -> Property 
prop_sub_perm_termvar = iprop_sub_perm Var 


-- * Typing and reduction

-- | (id id) has no type (it needs a type argument)
prop_untypeable :: Bool 
prop_untypeable = isNothing $ typeOf (App idTrm idTrm) 

-- | Not all terms are typeable
prop_all_typeable :: Trm -> Property 
prop_all_typeable t = expectFailure $ typeable t 


prop_typeable_nf :: Trm -> Property
prop_typeable_nf t = typeable t ==> normalisable t

prop_nf_typeable :: Trm -> Property
prop_nf_typeable t = normalisable t ==> typeable t

-- | Type soundness
-- If a term is typeable and normalisable then its normal form has the same type as it does. 
prop_type_soundness :: Trm -> Property 
prop_type_soundness t = typeable t ==> normalisable t ==> (typeOf t === (typeOf =<< nf t))

-- | typeof(id t) = typeof(t)
prop_id_type_unchanged :: Trm -> Property 
prop_id_type_unchanged t = typeable t ==> typeOf t === typeOf (App (TApp idTrm (typeOf' t)) t)

-- | If x : t then (id t x) --> x
prop_app_id :: Trm -> Property 
prop_app_id t = typeable t ==> nf' t === nf' (App (TApp idTrm (typeOf' t)) t)

{-- prop_typeable_sub :: Name NTrmLabel -> Trm -> Trm -> Property
prop_typeable_sub n t1 t2 = typeable t1 ==> typeable t2 ==> typeable $ sub n t1 t2 --}

{-- prop_typeable_sub' :: Name NTrmLabel -> Trm -> Trm -> Property
prop_typeable_sub' n t1 t2 = typeable t1 ==> typeable t2 ==> ((typeOf' t2) === (typeOf' (sub n' t1 t2))) where 
   n' = nameOverwriteLabel (Just ("",typeOf' t1)) n --}

-- * Church numerals

-- | 0 : nat
prop_typeof_zero :: Bool
prop_typeof_zero = typeOf zero == Just nat

-- | i+1 /= 0 
prop_church_numerals0 :: NonNegative Int -> Bool
prop_church_numerals0 (NonNegative i) = church (i + 1) /= zero

-- | i+1 /= i 
prop_church_numerals1 :: NonNegative Int -> Bool
prop_church_numerals1 (NonNegative i) = church (i + 1) /= church i 

-- | i : nat
prop_church_numerals_type :: NonNegative Int -> Bool
prop_church_numerals_type (NonNegative i) = typeOf (church i) == Just nat
 
