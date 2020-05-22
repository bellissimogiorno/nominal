{-|
Module      : System F 
Description : Syntax and reductions of System F using the Nominal package
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Syntax and reductions of System F using the Nominal package
-}

{-# LANGUAGE DataKinds             
           , InstanceSigs          
           , DeriveAnyClass        
           , DeriveGeneric         
           , MultiParamTypeClasses 
           , FlexibleInstances     
           , LambdaCase            
           , PolyKinds             
           , DefaultSignatures     
           , DeriveAnyClass        
           , DeriveGeneric         
           , EmptyCase             
           , FlexibleInstances     
           , FlexibleContexts       -- so we can write `Swappable d`
           , InstanceSigs          
           , LambdaCase            
           , MultiParamTypeClasses 
           , StandaloneDeriving    
           , TypeOperators         
           , UndecidableInstances  
#-}


module Language.Nominal.Examples.SystemF 
    ( 
-- * Introduction
-- $intro
    AKind (..),
-- * System F types 
    NTypLabel, NTyp, Typ (..), typRecurse,
-- * System F terms
    NTrmLabel, NTrm, Trm (..), typeOf, typeOf', typeable,  
-- * Normal forms
    nf, nf', normalisable,
-- * Pretty-printer
    PP (..),  
-- * Helper functions for building terms 
    tall, tlam, lam, (@.), (@:),
-- * Example terms
    idTrm, idTrm2, zero, suc, one, nat, church, transform, selfapp
-- * Tests
-- $tests
    )
    where

import Data.Maybe
import GHC.Generics
import Control.Monad (guard)

import Language.Nominal.Utilities 
import Language.Nominal.Name 
import Language.Nominal.Nom
import Language.Nominal.Abs 
import Language.Nominal.Sub 

{- $intro

System F is a classic example and has some interesting features:

* Two kinds of variable: /type variables/ and /term variables/.
* Three kinds of binding: /type forall/ binding a type variable in a type; /term lambda/ binding a term variable in a term; and /type lambda/ binding a type variable in a term.
* A static assignment of semantic information to term variables, namely: a /type assignment/.  Thus intuitively term variables carry labels (types), which themselves may contain type variables.
* And it's an expressive system of independent mathematical interest.

So implementing System F is a natural test for this package.
We start with atoms:
 
-}

-- * Atoms

-- | With @DataKinds@, this datatype gives us the following:
--
-- * A kind of atoms @AKind@, containing two sorts:
-- * @ATyp@ a sort of atoms to identify type variables @'NTyp'@, and
-- * @ATrm@ a sort of atoms to identify term variables @'NTrm'@.
--
-- See 'Language.Nominal.Name.Tom' for more discussion of how this works.
data AKind = ATyp -- ^ Atoms for type variable names 'NTyp' 
           | ATrm -- ^ Atoms for term variable names 'NTrm'


-- * System F types 

-- | A type variable is labelled just by a display name
type NTypLabel = String 
-- | A type variable name.  Internally, this consists of
--
-- * an atom of type @KAtom 'ATyp@, and
-- * a label of type @'NTypLabel'@, which is just a display name in @'String'@. 
type NTyp = KName 'ATyp NTypLabel

-- | Datatype of System F types 
--
-- We use @Generic@ to deduce a swapping action for atoms of sorts @''ATyp'@ and @''ATrm'@ (i.e. of kind @AKind@). 
-- Just once, we spell out the definition implicit in the generic instance:  
--
-- > instance KSwappable AKind Typ where
-- >    swpN n1 n2 (TVar n)   = TVar $ swpN n1 n2 n
-- >    swpN n1 n2 (t' :-> t) = swpN n1 n2 t' :-> swpN n1 n2 t
-- >    swpN n1 n2 (All x)    = All $ swpN n1 n2 x
--
-- This is boring, and automated, and that's the point: swappings distribute uniformly through everything including abstractors (the @x@ under the @All@).  
--
-- (The mathematical reason for this is that swappings are invertible, whereas renamings and substitutions aren't.)
--
data Typ = 
   TVar NTyp           -- ^ Type variable
 | Typ :-> Typ         -- ^ Type application
 | All (KAbs NTyp Typ) -- ^ Type forall-abstraction
 deriving (Eq, Generic, KSwappable AKind)

-- | A congruence descends into the type.  Action on binder is automagically capture-avoiding.
instance Cong Typ where
   congRecurse :: (Typ -> Typ) -> Typ -> Typ 
   congRecurse k = \case
      TVar n    -> TVar n
      s1 :-> s2 -> k s1 :-> k s2
      All x     -> All $ fmap k x 


 
-- | Substitution acts on type variables.  Capture-avoidance is automagical.
instance KSub NTyp Typ Typ where
   sub :: NTyp -> Typ -> Typ -> Typ 
   sub a t = cong $ \case
      (TVar n) -> toMaybe (a == n) t -- note name-equality is atom-wise and ignores labels 
      _        -> Nothing

-- | Nominal recursion scheme.  We never use it because it's implicit in pattern-matching plus `@@!`.
typRecurse :: (NTyp -> a) -> (Typ -> Typ -> a) -> (NTyp -> Typ -> a) -> Typ -> a 
typRecurse f1 _ _ (TVar n)    = f1 n
typRecurse _ f2 _ (s1 :-> s2) = f2 s1 s2
typRecurse _ _ f3 (All x')    = x' @@! f3 


------------------------------------
-- * System F terms


-- | A term variable is labelled by a display name, and its type
type NTrmLabel = ( String -- Display name of term variable
                 , Typ    -- Type of the term variable
                 )
-- | A term variable name 
type NTrm = KName 'ATrm NTrmLabel

-- | Substitute type variables with type in term variable.  
-- Non-trivial because a term variable carries a label which contains a type.  
-- Action is functorial, descending into the type label. 
instance KSub NTyp Typ NTrm where
   sub a ty' (Name lab atm) = Name (sub a ty' lab) atm

-- | System F terms.  
--
-- * We get swapping actions automatically, and also substitution of type names @NTyp@ for types @Typ@.  
-- * Substitution of term variables @NTrm@ for terms @Trm@ needs defined separately. 
--
data Trm =  Var NTrm             -- ^ Term variable, labelled by its display name and type 
          | App Trm Trm          -- ^ Apply a term to a term  
          | Lam (KAbs NTrm Trm)  -- ^ Nominal atoms-abstraction by a term variable. 
          | TApp Trm Typ         -- ^ Apply a term to a type
          | TLam (KAbs NTyp Trm) -- ^ Nominal atoms-abstraction by a type variable.   
  deriving ( Eq
           , Generic
           , KSwappable AKind   --- swappings derived automatically
           , KSub NTyp Typ      --- substitution of type names for types derived automatically
           )

-- This notion of congruence is good for term substitution. 
-- (Type substitution comes from the generic instance.)
instance Cong Trm where
   congRecurse k = \case
         Var n      -> Var n
         App s1 s2  -> App (k s1) (k s2)
         Lam x      -> Lam $ fmap k x
         TApp s1 t2 -> TApp (k s1) t2 
         TLam x     -> TLam $ fmap k x

-- | Substitute term variable with term in term
instance KSub NTrm Trm Trm where
   sub :: NTrm -> Trm -> Trm -> Trm 
   sub a t = cong $ \case 
         Var n -> toMaybe (a == n) t  -- note name-equality is atom-wise and ignores labels 
         _     -> Nothing

-- | Calculate type of term, maybe
typeOf :: Trm -> Maybe Typ 
typeOf (Var n)     = let (_, t) = nameLabel n in Just t
typeOf (TLam (tp :@> tm)) = do -- Maybe monad
   typetm <- typeOf tm 
   return $ All (abst tp typetm) 
typeOf (Lam (n :@> tm)) = do -- Maybe monad
   typetm <- typeOf tm
   let (_, t) = nameLabel n
   return $ t :-> typetm 
typeOf (App s1 s2) = do -- Maybe monad 
   t1a :-> t1b    <- typeOf s1
   t2             <- typeOf s2 
   guard (t1a == t2) 
   return t1b 
typeOf (TApp s t)  = do -- Maybe monad
   All x' <- typeOf s
   return $ subApp x' t -- substitution of type name for type, in type 

-- | Calculate type of term; raise error if none exists
typeOf' :: Trm -> Typ
typeOf' s = fromMaybe (error ("Type error" ++ ppp s)) (typeOf s) 

-- | @'True'@ if term is typeable; @'False'@ if not. 
typeable :: Trm -> Bool
typeable = isJust . typeOf 


-- * Normal forms

-- | Normal form, maybe 
nf :: Trm -> Maybe Trm  
nf s = guard (typeable s) >> return (repeatedly nf_ s)
   where -- behaviour on untypeable terms is undefined
   nf_ :: Trm -> Trm
   nf_ = cong $ \case 
            TApp (TLam x') t2 -> return . nf_ $ subApp x' t2
            App  (Lam x')  s2 -> return . nf_ $ subApp x' (nf_ s2)
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
type TypeVarContext = Name NTypLabel -> Typ
type TermVarContext = Name NTrmLabel -> Sem 

sem :: TypeVarContext -> TermVarContext -> Trm -> Maybe Sem
sem tyc tmc (Var n)      = Just $ tmc n       -- ^ Look up in the var context
sem tyc tmc (App s1 s2)  = do -- Maybe monad
   SemLam t f <- sem tyc tmc s1 
   f <$> (sem tyc tmc s2)
sem tyc tmc (Lam x)      = x @@! \n s -> do -- Maybe monad
   (_, nty) <- nameLabel n
   return $ SemLam nty (\x -> sem tyc (sub n x tmc) s)
sem tyc tmc (TApp s1 t2) = do -- Maybe monad
   SemTLam f <- sem tyc tmc s1 
   return $ f t2
sem tyc tmc (TLam x)     = x @@! \n s -> SemTLam (\x -> sem (sub n x tyc) tmc s)

-- A useful property would be that sem (t t') = sem t (sem t')
--}

---------------------------------------------
-- * Pretty-printer

-- | Typeclass for things that can be pretty-printed
class PP a where
   ppp :: a -> String
   pp  :: a -> IO ()
   pp = putStrLn . ppp 

-- | Pretty-print type variable 
instance PP NTyp where
   ppp n = (nameLabel n) ++ "(" ++ show (nameAtom n) ++ ")" 

-- | Pretty-print type 
instance PP Typ where
  ppp (TVar n)  = ppp n
  ppp (All (n :@> t)) = '∀':(ppp n ++ "." ++ ppp t)
  ppp (t :-> u) = pppL t ++ " -> " ++ pppR u where
    pppL (All _)      = "(" ++ ppp t ++ ")"
    pppL (_ :-> _)    = "(" ++ ppp t ++ ")"
    pppL _            = ppp t
    pppR (All _)      = "(" ++ ppp u ++ ")"
    pppR _            = ppp u

-- | Pretty-print term variable 
instance PP NTrm where
   ppp n = (\(s, t) -> s ++ ":" ++ ppp t) (nameLabel n) ++ "(" ++ show (nameAtom n) ++ ")" 

-- Forall ∀
-- Capital Lambda Λ = \0923
-- lambda λ = \0955
-- | Pretty-print term 
instance PP Trm where
   ppp (Lam (n :@> t))      = "λ" ++ pppN n ++ pppB t where
      pppB (Lam (n' :@> t')) = "," ++ " " ++ pppN n' ++ pppB t' 
      pppB expr     = '.':ppp expr
      pppN n'       = let (s', t') = nameLabel n' in (s' ++ ":" ++ ppp t')
   ppp (TLam (n :@> t))     = "Λ" ++ ppp n ++ pppB t where
      pppB (TLam (n' :@> t')) = " " ++ ppp n' ++ pppB t'
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



-- * Helper functions for building terms 

-- | Build type quantification from function: f ↦ ∀ a.(f a) for fresh a
tall :: NTypLabel -> (Typ -> Typ) -> Typ 
tall s f = All $ absFresh s (f . TVar)

-- | Build type lambda from function: f ↦ Λ a.(f a) for fresh a
tlam :: NTypLabel -> (Typ -> Trm) -> Trm
tlam s f = TLam $ absFresh s (f . TVar)

-- | Build term lambda from function: f ↦ λ a.(f a) for fresh a
lam :: NTrmLabel -> (Trm -> Trm) -> Trm
lam (s,ty) f = Lam $ absFresh (s, ty) (f . Var)

-- | Term-to-term application
(@.) :: Trm -> Trm -> Trm
s1 @. s2   = App s1 s2

-- | Term-to-type application
(@:) :: Trm -> Typ -> Trm
s1 @: t2  = TApp s1 t2


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
         s @. (((n @: xx) @. s) @. z)

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
selfapp = lam ("x", transform) $ \x -> (x @: transform) @. x  

{- $tests Property-based tests are in "Language.Nominal.Properties.Examples.SystemFSpec". -}
