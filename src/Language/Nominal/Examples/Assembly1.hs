{-|
Module      : Simple Assembly Example 1 
Description : A simple assembly language, with binding 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Based on <https://github.com/ekmett/bound/blob/master/examples/Imperative.hs an example in the Bound package>.  
What makes this interesting is the binding behaviour of 'Add', which adds two numbers and binds the result to a fresh register with scope over subsequent instructions. 


-}

{-# LANGUAGE InstanceSigs          
           , DeriveGeneric         
           , MultiParamTypeClasses 
           , DeriveAnyClass       -- to derive 'Swappable' 
           , FlexibleInstances     
#-}


module Language.Nominal.Examples.Assembly1
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

-- | Evaluate a program 
evalProg :: Prog -> Int
evalProg (Ret o)        = evalOperand o
evalProg (Add o1 o2 x') = evalProg (x' `conc` Lit (evalOperand o1 + evalOperand o2)) -- `conc` here substitutes a value for a bound name in an abstraction

-- | Add 1 2 [v] Add v v [w] Ret w  
example1 :: Prog 
example1 = freshNames ["v", "w"] @@! \_ [v, w] -> 
           Add (Lit 1) (Lit 2) $ v :@> Add (Var v) (Var v) $ w :@> Ret (Var w) -- :@> is name-abstraction, also called 'abst'. 

-- | 6 
example1eval :: Int 
example1eval = evalProg example1 

