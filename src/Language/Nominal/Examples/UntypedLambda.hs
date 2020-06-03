{-|
Module      : Untyped Lambda-Calculus 
Description : Syntax and reductions of the untyped lambda-calculus using the Nominal package
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Untyped lambda-calculus: syntax, substitution, nominal-style recursion, weak head normal form function, and a couple of examples.

Compare with an example in <https://hackage.haskell.org/package/bound the Bound package>. 

-}

{-# LANGUAGE InstanceSigs          
           , DeriveGeneric         
           , LambdaCase 
           , MultiParamTypeClasses 
           , DeriveAnyClass       -- to derive 'Swappable' 
           , DeriveDataTypeable   -- to derive 'Data' 
           , FlexibleInstances     
#-}


module Language.Nominal.Examples.UntypedLambda
    ( 
     Var, Exp (..), whnf, lam, example1, example1whnf, example2, example2whnf 
    )
    where

import GHC.Generics
import Data.Generics     hiding (Generic, typeOf)

import Language.Nominal.Utilities
import Language.Nominal.Name 
import Language.Nominal.Nom
import Language.Nominal.Binder
import Language.Nominal.Abs 
import Language.Nominal.Sub 

-- | Variables are string-labelled names
type Var = Name String 

infixl 9 :@
-- | Terms of the untyped lambda-calculus 
data Exp = V Var              -- ^ Variable 
         | Exp :@ Exp         -- ^ Application 
         | Lam (KAbs Var Exp) -- ^ Lambda, using abstraction-type 
 deriving (Eq, Generic, Data, Swappable, Show)

-- | helper for building lambda-abstractions 
lam :: Var -> Exp -> Exp 
lam x a = Lam (x @> a)

-- | Substitution.  Capture-avoidance is automatic.
instance KSub Var Exp Exp where
   sub :: Var -> Exp -> Exp -> Exp 
   sub v t = rewrite $ \case -- 'rewrite' comes from Scrap-Your-Boilerplate generics.  It recurses properly under the binder. 
      V v' | v' == v -> Just t   -- If @V v'@, replace with @t@ ... 
      _              -> Nothing  -- ... otherwise recurse.

{- The substitution instance above is equivalent to the following:
 
-- | Explicit recursion.     
expRec :: (Var -> a) -> (Exp -> Exp -> a) -> (Var -> Exp -> a) -> Exp -> a 
expRec f0 _ _ (V n)      = f1 n
expRec _ f1 _ (s1 :@ s2) = f2 s1 s2
expRec _ _ f2 (Lam x')   = f3 `genApp` x' 

instance KSub Var Exp Exp where
   sub :: Var -> Exp -> Exp -> Exp 
   sub v t = expRec (\v'   -> if v' == v then t else V v') 
                    (\a b  -> sub v t a :@ sub v t b) 
                    (\v' a -> lam v' $ sub v t a)
-}

-- | weak head normal form of a lambda-term.
whnf :: Exp -> Exp 
whnf (f :@ a) = case whnf f of
  Lam b' -> whnf $ b' `conc` a  
  f'     -> f' :@ a
whnf e = e

-- | (\x x) y
example1 :: Exp
example1 = (\[x, y] -> lam x $ V x :@ V y) `genAppC` freshNames ["x", "y"] 
-- | y
example1whnf :: Exp
example1whnf = whnf example1

-- | (\x xy) x
example2 :: Exp
example2 = (\[x, y] -> lam x (V x :@ V y) :@ V x) `genAppC` freshNames ["x", "y"] 
-- | xy
example2whnf :: Exp
example2whnf = whnf example2

