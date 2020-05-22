# nominal

## Basic information

The interaction of name-binding and alpha-equivalence with data can be tricky.  Examples include:

* Inductively defining syntax and reductions of a syntax with binding, e.g. lambda-calculus or System F.
* Graph-like structures, especially if they have danging pointers.

This package implements a nominal datatypes package in Haskell, based on names and swappings.  With it, you can define data with name-binding and program on this data in a nice manner that closely mirrors informal practice. 
With it, you can define data with name-binding and program on this data in a manner closely mirroring informal practice.

The package design is based on a well-studied mathematical reference model as described in [a new approach to abstract syntax with variable binding](https://link.springer.com/article/10.1007/s001650200016) ([author's pdfs](http://www.gabbay.org.uk/papers.html#newaas-jv)).

For usage, please see: 

* [The tutorial](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/Tutorial.hs).  This covers the main points of the package, from the point of view of a working programmer wishing to see the functions in use.  
* [An implementation of the untyped lambda-calculus](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/UntypedLambda.hs) is a classic example (reproduced below).
* [An implementation of System F](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/SystemF.hs) is an illustrative example of those functions applied in something resembling typical practice.
* [An implementation of a EUTxO blockchain system](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/IdealisedEUTxO.hs) is another, quite different, example of those functions applied in something resembling typical practice.
* More examples are in preparation. 


## Building and running

1. Install [Stack](https://github.com/commercialhaskell/stack).

2. Clone this repo:

        $ git clone https://github.com/bellissimogiorno/nominal.git
        $ cd nominal 

3. Build:

        $ stack build 

4. Read the documentation:

        $ stack haddock --open 

5. Run some unit- and property-based tests: 

        $ stack test 

5. Explore it in ghci:

        $ stack ghci Language/Nominal/Examples/SystemF.hs 
        $ stack ghci Language/Nominal/Examples/IdealisedEUTxO.hs 

## Example

Copied from [the untyped lambda calculus example](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/UntypedLambda.hs), and see [a corresponding example from the Bound package](https://hackage.haskell.org/package/bound).  

```haskell
{-# LANGUAGE InstanceSigs          
           , DeriveGeneric         
           , MultiParamTypeClasses 
           , DeriveAnyClass       -- to derive 'Swappable' 
           , FlexibleInstances     
#-}


module Language.Nominal.Examples.UntypedLambda
    ( 
     Var, Exp (..), expRec, whnf, lam, example1, example1whnf, example2, example2whnf 
    )
    where

import GHC.Generics

import Language.Nominal.Name 
import Language.Nominal.Nom
import Language.Nominal.Abs 
import Language.Nominal.Sub 

-- | Variables are string-labelled names
type Var = Name String 

infixl 9 :@
-- | Terms of the untyped lambda-calculus 
data Exp = V Var 
         | Exp :@ Exp 
         | Lam (KAbs Var Exp)
 deriving (Eq, Generic, Swappable, Show)

-- | helper for building lambda-abstractions 
lam :: Var -> Exp -> Exp 
lam x a = Lam (abst x a)

-- | Recursion.  A lambda-abstraction gets expanded as a variable and a body. 
expRec :: (Var -> a) -> (Exp -> Exp -> a) -> (Var -> Exp -> a) -> Exp -> a 
expRec f1 _ _ (V n)      = f1 n
expRec _ f2 _ (s1 :@ s2) = f2 s1 s2
expRec _ _ f3 (Lam x')   = f3 `genApp` x' 

-- | Substitution.  Capture-avoidance is automatic.
instance KSub Var Exp Exp where
   sub :: Var -> Exp -> Exp -> Exp 
   sub v t = expRec (\v'   -> if v' == v then t else V v') 
                    (\a b  -> sub v t a :@ sub v t b) 
                    (\v' a -> lam v' $ sub v t a)

-- | weak head normal form of a lambda-term.
whnf :: Exp -> Exp 
whnf (f :@ a) = case whnf f of
  Lam b' -> whnf $ b' `subApp` a  
  f'     -> f' :@ a
whnf e = e

-- | (\x x) y
example1 :: Exp
example1 = (\[x, y] -> lam x $ (V x) :@ V y) `genAppC` freshNames ["x", "y"] 
-- | y
example1whnf :: Exp
example1whnf = whnf example1

-- | (\x xy) x
example2 :: Exp
example2 = (\[x, y] -> (lam x $ V x :@ V y) :@ V x) `genAppC` freshNames ["x", "y"] 
-- | xy
example2whnf :: Exp
example2whnf = whnf example2
```

## Acknowledgements

Thanks to Lars Brünjes for help, support, and code contributions. 
