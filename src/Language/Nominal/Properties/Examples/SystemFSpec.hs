module Language.Nominal.Properties.Examples.SystemFSpec
    where

import Test.QuickCheck

import Language.Nominal.Names 
import Language.Nominal.Nom
import Language.Nominal.Sub
import Language.Nominal.Examples.SystemF

-- * Substitution

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


-- * Typing and reduction

-- | (id id) has no type (it needs a type argument)
prop_untypable :: Bool 
prop_untypable = isNothing $ typeOf (App idTrm idTrm) 

-- | Not all terms are typable
prop_all_typable :: Trm -> Property 
prop_all_typable t = expectFailure $ typable t 


prop_typable_nf :: Trm -> Property
prop_typable_nf t = typable t ==> normalisable t

prop_nf_typable :: Trm -> Property
prop_nf_typable t = normalisable t ==> typable t

-- | Type soundness
-- If a term is typable and normalisable then its normal form has the same type as it does. 
prop_type_soundness :: Trm -> Property 
prop_type_soundness t = typable t ==> normalisable t ==> (typeOf t === (typeOf =<< nf t))

-- | typeof(id t) = typeof(t)
prop_id_type_unchanged :: Trm -> Property 
prop_id_type_unchanged t = typable t ==> typeOf t === typeOf (App (TApp idTrm (typeOf' t)) t)

-- | If x : t then (id t x) --> x
prop_app_id :: Trm -> Property 
prop_app_id t = typable t ==> nf' t === nf' $ App (TApp idTrm (typeOf' t)) t

{-- prop_typable_sub :: Name NTrm -> Trm -> Trm -> Property
prop_typable_sub n t1 t2 = typable t1 ==> typable t2 ==> typable $ sub n t1 t2 --}

{-- prop_typable_sub' :: Name NTrm -> Trm -> Trm -> Property
prop_typable_sub' n t1 t2 = typable t1 ==> typable t2 ==> ((typeOf' t2) === (typeOf' (sub n' t1 t2))) where 
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
 
-- mjg do scope extrusion, perhaps using a nameless type
