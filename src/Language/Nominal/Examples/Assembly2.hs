{-|
Module      : Simple Assembly Example 2 
Description : A simple assembly language, with binding and variable-swapping 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Based on <https://github.com/ekmett/bound/blob/master/examples/Imperative.hs an example in the Bound package>.  This is interesting for the binding behaviour of 'Add' and the swapping behaviour of 'Swp'. 
'Add' adds two numbers and binds the result to a fresh register with scope over subsequent instructions. 
'Swp' swaps the contents of two registers with scope over subsequent instructions. 

-}

{-# LANGUAGE InstanceSigs          
           , DeriveGeneric         
           , MultiParamTypeClasses 
           , DeriveAnyClass       -- to derive 'Swappable' 
           , FlexibleInstances     
#-}


module Language.Nominal.Examples.Assembly2
    where

import GHC.Generics

import Language.Nominal.Name 
import Language.Nominal.Nom
import Language.Nominal.Binder
import Language.Nominal.Abs 
import Language.Nominal.Sub 

-- | Variables are string-labelled names
type V = Name String 

-- | An operand is an integer literal or a variable
data Operand = Lit Int | Var V 
  deriving (Eq, Generic, Swappable, Show)

-- | Substitution as standard on 'Operand'
instance KSub V Operand Operand where
   sub :: V -> Operand -> Operand -> Operand
   sub _ _ (Lit n)  = Lit n
   sub v o (Var v') = if v == v' then o else Var v' 

-- | Terms of our assembly language 
data Prog = Ret Operand        -- ^ Return a value 
          | Swp Operand Operand Prog -- ^ Swap the contents of two variables
          | Add Operand Operand (KAbs V Prog) -- ^ Add two operands and store the value in a fresh variable which is local to subsequent computation (the third argument) 
  deriving (Eq, 
            Generic, 
            Swappable, 
            Show, 
            KSub V Operand -- ^ Substitution on 'Prog'rams is generic
           )

-- | Evaluate an operand.  
--
-- * A literal maps to its corresponding integer.  
-- * If asked to evaluate a free variable, complain. 
evalOperand :: Operand -> Int
evalOperand (Lit i) = i
evalOperand (Var _) = undefined 

-- | Normalise a program by executing any embedded Swp commands. 
normaliseProg :: Prog -> Prog 
normaliseProg (Swp (Var v1) (Var v2) x)  
             = normaliseProg $ swpN v1 v2 x
normaliseProg (Add o1 o2 x') 
             = Add o1 o2 $ normaliseProg <$> x'
normaliseProg p = p

-- | Evaluate a program 
evalProg :: Prog -> Int 
evalProg = go . normaliseProg
   where 
      go :: Prog -> Int
      go (Ret o)        = evalOperand o
      go (Add o1 o2 x') = go $ x' `conc` Lit (evalOperand o1 + evalOperand o2) -- `conc` here substitutes a value for a bound name in an abstraction
      go _              = undefined

-- | Add 1 2 [v] Add v v [w] Swp v w Ret w  
example1 :: Prog 
example1 = freshNames ["v", "w"] @@! \_ [v, w] -> 
           Add (Lit 1) (Lit 2) $ v :@> Add (Var v) (Var v) $ w :@> Swp (Var v) (Var w) $ Ret (Var w)   -- :@> is name-abstraction, also called 'abst'. 

-- | 3 
example1eval :: Int 
example1eval = evalProg example1 

