{-|
Module      : System F 
Description : Syntax and reductions of System F using the Nominal datatypes package
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Syntax and reductions of @System F@ using the Nominal datatypes package
-}

{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}


module Language.Nominal.Examples.SystemF 
--    ( 
--    )
    where

import Data.Maybe

import Language.Nominal.Utilities 
import Language.Nominal.Names 
-- import Language.Nominal.Nom
import Language.Nominal.Abs 
import Language.Nominal.Sub 

-----------------------------------------------
-- System F 

------------------------------------
-- System F types 

-- | A type variable is labelled just by a display name
type NTyp = String

-- | Datatype of System F types 
data Typ = 
   TVar (Name NTyp)   -- ^ Type variable
 | Typ :-> Typ        -- ^ Type application
 | All (Abs NTyp Typ) -- ^ Type forall-abstraction
 deriving (Eq)

instance Cong Typ where
   congRecurse :: (Typ -> Typ) -> Typ -> Typ 
   congRecurse k = \case
      TVar n    -> TVar n
      s1 :-> s2 -> k s1 :-> k s2
      All x     -> All $ fmap k x 

-- mjg invites generics
-- lars suggests newtypedriving.  extension generalisednewtypederiving
-- lars suggests generics.
-- do generics.  derive generics, derive anyclass.  deriving generics yourtypeclass.  look at haskell wiki equality & serialisation
-- | Swap type atoms in a type
instance Swappable NTyp Typ where
   swp n1 n2 (TVar n)      = TVar $ swp' n1 n2 n
   swp n1 n2 (t' :-> t)    = swp n1 n2 t' :-> swp n1 n2 t
   swp n1 n2 (All (Abs f)) = All $ Abs $ swp n1 n2 f

-- | Swap term atoms in a type name (trivial action)
instance Swappable NTrm (Name NTyp) where
   swp _ _ t = t
-- | Swap term atoms in a type (trivial action)
instance Swappable NTrm Typ where
   swp _ _ t = t
 
-- | Substitution acts on type variables.  Nominal package takes care of capture-avoidance.
instance Sub NTyp Typ Typ where
   sub :: Name NTyp -> Typ -> Typ -> Typ 
   sub a t = cong $ \case
      (TVar n) -> toMaybe (a == n) t 
      _        -> Nothing

-- | Nominal recursion scheme.  Implicit in pattern-matching plus `@@`.
typRecurse :: (Name NTyp -> a) -> (Typ -> Typ -> a) -> (Name NTyp -> Typ -> a) -> Typ -> a 
typRecurse f1 _ _ (TVar n)    = f1 n
typRecurse _ f2 _ (s1 :-> s2) = f2 s1 s2
typRecurse _ _ f3 (All x')    = x' @@ f3 


------------------------------------
-- * System F terms


-- | A term variable is labelled by a display name, and its type
type NTrm = (String, Typ)

-- | Swap type variables in a term variable.  Non-trivial because a term variable carries a label which contains a type.  Action is functorial, descending into the type label. 
instance Swappable NTyp (Name NTrm) where
   swp n1 n2 n = swp n1 n2 <$> n

-- | Substitute type variables with type in term variable.  Non-trivial because a term variable carries a label which contains a type.  Action is functorial, descending into the type label. 
instance Sub NTyp Typ (Name NTrm) where
   sub a ty' (Name (lab, atm)) = Name (sub a ty' lab, atm) 

-- | System F terms
data Trm =  Var  (Name NTrm)     -- ^ Term variable, labelled by its display name and type 
          | App   Trm Trm        -- ^ Apply a term to a term  
          | Lam  (Abs NTrm Trm)  -- ^ Nominal atoms-abstraction by a term variable. 
          | TApp  Trm Typ        -- ^ Apply a term to a type
          | TLam (Abs NTyp Trm)  -- ^ Nominal atoms-abstraction by a type variable.   
--  deriving (Eq, Show)
  deriving (Eq)

-- | Swap term variables in a term.  
instance Swappable NTrm Trm where
   swp n1 n2 (Var n)        = Var $ swp' n1 n2 n               -- Actual swapping here 
   swp n1 n2 (App t' t)     = App (swp n1 n2 t') (swp n1 n2 t) -- All other cases are generic 
   swp n1 n2 (Lam (Abs f))  = Lam $ Abs $ swp n1 n2 f
   swp n1 n2 (TApp t' t)    = TApp (swp n1 n2 t') (swp n1 n2 t)
   swp n1 n2 (TLam (Abs f)) = TLam $ Abs $ swp n1 n2 f

-- | Swap type variables in a term.  
instance Swappable NTyp Trm where
   swp n1 n2 (Var n)        = Var (swp n1 n2 n)               
-- mjg delete? Functorial action; applies to label 
   swp n1 n2 (App t' t)     = App (swp n1 n2 t') (swp n1 n2 t)
   swp n1 n2 (Lam (Abs f))  = Lam $ Abs $ swp n1 n2 f
   swp n1 n2 (TApp t' t)    = TApp (swp n1 n2 t') (swp n1 n2 t)
   swp n1 n2 (TLam (Abs f)) = TLam $ Abs $ swp n1 n2 f

-- only good for term substitution, not type substitution
instance Cong Trm where
   congRecurse k = \case
         Var n      -> Var n
         App s1 s2  -> App (k s1) (k s2)
         Lam x      -> Lam $ fmap k x
         TApp s1 t2 -> TApp (k s1) t2 
         TLam x     -> TLam $ fmap k x

-- | Calculate type of term, maybe
typeOf :: Trm -> Maybe Typ 
typeOf (Var n)     = do -- Maybe monad
   (_, t) <- nameLabel n
   return t 
typeOf (TLam x')   = x' @@ \tp tm -> do -- Maybe monad
   typetm <- typeOf tm 
   return $ All (absByName tp typetm) 
typeOf (Lam x')    = x' @@ \n  tm -> do -- Maybe monad
   typetm <- typeOf tm
   (_, t) <- nameLabel n
   return $ t :-> typetm 
typeOf (App s1 s2) = do -- Maybe monad 
   t1a :-> t1b    <- typeOf s1
   t2             <- typeOf s2 
   toMaybe (t1a == t2) t1b 
typeOf (TApp s t)  = do -- Maybe monad
   All x' <- typeOf s
--   x' @@ \n' t' -> return $ sub n' t t'
   Just $ subM x' t 

-- | Calculate type of term; raise error if none exists
typeOf' :: Trm -> Typ
typeOf' s = fromMaybe (error ("Type error" ++ ppp s)) (typeOf s) 

-- | True if term is typable; false if not. 
typable :: Trm -> Bool
typable = isJust . typeOf 


-- Substitution of types for type variables in terms
-- Here sub (by design) substitutes in the labels of variables at the site where they are bound.
-- This means that if unsafeUnNom has detached a variable from its surrounding binding, then sub may not find that binding and may not substitute in the variable's label.
{-  instance Sub NTyp Typ Trm where
   sub :: Name NTyp -> Typ -> Trm -> Trm 
   sub a t = cong $ \case
--         Lam x -> (x, \(s,t') -> (s, sub a t t')) @@@ 
--                  \tm s -> Just . Lam . (absByName tm) $ (sub a t s)
         Lam x -> Just . Lam $ sub a t x
         _     -> Nothing
-}

-- | Substitute type variable with type in term.  Not boilerplate; must handle type labels correctly.
instance Sub NTyp Typ Trm where
   sub :: Name NTyp -> Typ -> Trm -> Trm 
   sub a t (Var n)      = Var (sub a t n) 
   sub a t (Lam x)      = Lam $ sub a t x
   sub a t (App t1 t2)  = App (sub a t t1) (sub a t t2)
   sub a t (TApp t1 t2) = TApp (sub a t t1) (sub a t t2)
   sub a t (TLam x)     = TLam $ sub a t x

-- | Substitute term variable with term in term
instance Sub NTrm Trm Trm where
   sub :: Name NTrm -> Trm -> Trm -> Trm 
   sub a t = cong $ \case 
         Var n -> toMaybe (a == n) t 
         _     -> Nothing



-- * Normal forms

-- | Normal form, maybe 
nf :: Trm -> Maybe Trm  
nf s = case typeOf s of
   Just _  -> Just (repeatedly nf_ s)
   Nothing -> Nothing 
   where -- behaviour on untypable terms is undefined
   nf_ :: Trm -> Trm
   nf_ = cong $ \case 
            TApp (TLam x') t2 -> Just . nf_ $ subM x' t2
            App  (Lam x')  s2 -> Just . nf_ $ subM x' (nf_ s2)
            _                 -> Nothing

-- | Normal form; raise error if none
nf' :: Trm -> Trm 
nf' s = fromMaybe (error ("Type error: " ++ ppp s)) (nf s) 

-- | True if term is normalisable; false if not. 
normalisable :: Trm -> Bool
normalisable = isJust . nf  



{---------------------------------------------
-- Semantics 

data Sem = SemLam Typ (Sem -> Sem) | SemTLam (Typ -> Sem) 

-- We get sub automagically
type TypeVarContext = Name NTyp -> Typ
type TermVarContext = Name NTrm -> Sem 

-- mjg to restore
sem :: TypeVarContext -> TermVarContext -> Trm -> Maybe Sem
sem tyc tmc (Var n)      = Just $ tmc n       -- ^ Look up in the var context
sem tyc tmc (App s1 s2)  = do -- Maybe monad
   SemLam t f <- sem tyc tmc s1 
   f <$> (sem tyc tmc s2)
sem tyc tmc (Lam x)      = x @@ \n s -> do -- Maybe monad
   (_, nty) <- nameLabel n
   return $ SemLam nty (\x -> sem tyc (sub n x tmc) s)
sem tyc tmc (TApp s1 t2) = do -- Maybe monad
   SemTLam f <- sem tyc tmc s1 
   return $ f t2
sem tyc tmc (TLam x)     = x @@ \n s -> SemTLam (\x -> sem (sub n x tyc) tmc s)

-- A useful property would be that sem (t t') = sem t (sem t')
--}

---------------------------------------------
-- Pretty-printer

-- | Typeclass for things that can be pretty-printed
class PP a where
   ppp :: a -> String
   pp  :: a -> IO ()
   pp = putStrLn . ppp 

-- | Pretty-print type variable 
instance PP (Name NTyp) where
   ppp n = fromMaybe "Nothing" (nameLabel n) ++ "(" ++ show (nameAtom n) ++ ")" 

-- | Pretty-print type 
instance PP Typ where
  ppp (TVar n)  = ppp n
  --- ppp (All x)   = x @@ \n t -> '\8704':(ppp n ++ "." ++ ppp t)
  ppp (All x)   = x @@ \n t -> '∀':(ppp n ++ "." ++ ppp t)
  ppp (t :-> u) = pppL t ++ " -> " ++ pppR u where
    pppL (All _)      = "(" ++ ppp t ++ ")"
    pppL (_ :-> _)    = "(" ++ ppp t ++ ")"
    pppL _            = ppp t
    pppR (All _)      = "(" ++ ppp u ++ ")"
    pppR _            = ppp u

-- mjg explain shownothing
-- | Pretty-print term variable 
instance PP (Name NTrm) where
--   ppp n = show $ nameLabel n
   ppp n = maybe "Nothing" (\(s, t) -> s ++ ":" ++ ppp t) (nameLabel n) ++ "(" ++ show (nameAtom n) ++ ")" 

-- Forall ∀
-- Capital Lambda Λ = \0923
-- lambda λ = \0955
-- | Pretty-print term 
instance PP Trm where
   ppp (Lam x)      = x @@ \n t -> "λ" ++ pppN n ++ pppB t where
      pppB (Lam x') = "," ++ x' @@ \n' t' -> " " ++ pppN n' ++ pppB t' 
      pppB expr     = '.':ppp expr
      pppN n        = fromMaybe "Nothing" $ do -- Maybe monad
         (s, t) <- nameLabel n 
         return (s ++ ":" ++ ppp t)
   ppp (TLam x)     = x @@ \n t -> "Λ" ++ ppp n ++ pppB t where
      pppB (TLam x') = x' @@ \n' t' -> " " ++ ppp n' ++ pppB t'
      pppB expr     = '.':ppp expr
   ppp (Var s)      = ppp s
   ppp (App x y)    = pppL x ++ pppR y where
      pppL (Lam _)  = "(" ++ ppp x ++ ")"
      pppL _        = ppp x
      pppR (Var s)  = ' ':ppp s
      pppR _        = "(" ++ ppp y ++ ")"
   ppp (TApp x y)   = pppL x ++ "[" ++ ppp y ++ "]" where
      pppL (Lam _)  = "(" ++ ppp x ++ ")"
      pppL _        = ppp x
--  ppp (Let x y z) =
--    "let " ++ x ++ " = " ++ ppp y ++ " in " ++ ppp z


instance {-# OVERLAPS #-} Show Trm where
   show = ppp
instance {-# OVERLAPS #-} Show (Maybe Trm) where
   show = maybe "No term!" ppp

instance {-# OVERLAPS #-} Show Typ where
   show = ppp
instance {-# OVERLAPS #-} Show (Maybe Typ) where
   show = maybe "No type!" ppp



{- instance PP Trm where
   ppp x = ppp_ x ++ " : " ++ ppp (typeOf x) 
   where
      ppp_ (Lam x)          = x @@ \n s -> "λ" ++ ppp_ n ++ pppB s where
         pppB (Lam x)        = x @@ \n s -> " " ++ ppp_ n ++ pppB s
         pppB expr           = '.':ppp_ expr
   --    ppp_T (TV "_")       = ""
   --  ppp_T t              = ':':ppp_ t
      ppp_ (TLam x)          = x @@ \n t -> "λ" ++ ppp_ n ++ pppB t where
         pppB (TLam x)       = x @@ \n t -> " " ++ ppp_ n ++ pppB t
         pppB expr           = '.':ppp_ expr
      ppp_ (Var s)     = ppp_ s
      ppp_ (App x y)   = pppL x ++ pppR y where
         pppL (Lam _)  = "(" ++ ppp_ x ++ ")"
         pppL _         = ppp_ x
         pppR (Var s)   = ' ':ppp_ s
         pppR _         = "(" ++ ppp_ y ++ ")"
      ppp_ (TApp x y)   = pppL x ++ "[" ++ ppp_ y ++ "]" where
         pppL (Lam _)   = "(" ++ ppp_ x ++ ")"
         pppL _         = ppp_ x
   --  ppp_ (Let x y z) =
   --    "let " ++ x ++ " = " ++ ppp_ y ++ " in " ++ ppp_ z
-}


-- * Helper functions for building terms 

-- | Build type quantification from function: f ↦ ∀ a.(f a) for fresh a
tall :: NTyp -> (Typ -> Typ) -> Typ 
tall s f = All $ absFresh s (f . TVar)

-- | Build type lambda from function: f ↦ Λ a.(f a) for fresh a
tlam :: NTyp -> (Typ -> Trm) -> Trm
tlam s f = TLam $ absFresh s (f . TVar)

-- | Build term lambda from function: f ↦ λ a.(f a) for fresh a
lam :: NTrm -> (Trm -> Trm) -> Trm
lam (s,ty) f = Lam $ absFresh (s, ty) (f . Var)

-- | Term-to-term application
(@.) :: Trm -> Trm -> Trm
s1 @. s2   = App s1 s2

-- | Term-to-type application
(@@.) :: Trm -> Typ -> Trm
s1 @@. t2  = TApp s1 t2


-- * Example terms

-- | polymorphic identity term = λX x:X.x
idTrm :: Trm
idTrm = TLam $ absFresh "X" (\xx -> Lam $ absFresh ("x", TVar xx) (\x -> Var x))
-- | Another rendering of polymorphic identity term
idTrm2 :: Trm
idTrm2 = tlam "X" $ \xx -> lam ("x", xx) $ \x -> x -- hlint complains about \x -> x.  retained for clarity

-- | 0 = λX λs:X->X λz:X.z
zero :: Trm
zero = tlam "X" $ \xx -> lam ("s", xx :-> xx) $ \_s -> lam ("z", xx) $ \z -> z  -- hlint complains about \x -> x.  retained for clarity


-- | suc = λx:(∀X.(X->X)->X->X) X s:X->X z:X.s(n[X] s z)
suc :: Trm
suc = lam ("n",nat) $ \n -> 
      tlam "X" $ \xx -> 
      lam ("s", xx :-> xx) $ \s -> 
      lam ("z", xx) $ \z -> 
         s @. (((n @@. xx) @. s) @. z)

-- | 1
one :: Trm
one = nf' (suc @. zero)

-- | nat
nat :: Typ
nat = tall "X" $ \xx -> (xx :-> xx) :-> (xx :-> xx) 

-- | Cast an Int to the corresponding Church numeral.
church :: Int -> Trm
church 0 = zero
church i = suc @. church (i-1)

-- | Transformer type = ∀X.X->X
transform :: Typ
transform = tall "X" $ \xx -> xx :-> xx 

-- | Self-application = λx:∀X.X->X.x[∀X.X->X] x
selfapp :: Trm
selfapp = lam ("x", transform) $ \x -> (x @@. transform) @. x  

