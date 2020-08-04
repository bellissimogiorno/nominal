# nominal

## Basic information

The interaction of name-binding and alpha-equivalence with data can be tricky.  Examples include:

* Inductively defining syntax and reductions of a syntax with binding, e.g. lambda-calculus or System F.
* Graph-like structures, especially if they have danging pointers.

This package implements a nominal datatypes package in Haskell, based on names and swappings.  
With it, you can define data with name-binding and program on this data in a manner closely mirroring informal practice.

The package design is based on a well-studied mathematical reference model as described in [a new approach to abstract syntax with variable binding](https://link.springer.com/article/10.1007/s001650200016) ([author's pdfs](http://www.gabbay.org.uk/papers.html#newaas-jv)).

For usage, please see:

* [The tutorial](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/Tutorial.hs).  This covers the main points of the package, from the point of view of a working programmer wishing to see the functions in use.
* [An implementation of the untyped lambda-calculus](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/UntypedLambda.hs) is a classic example (reproduced below).
* [A simple assembly language (version 1)](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/Assembly1.hs) (adapted from [a corresponding example from the Bound package](https://github.com/ekmett/bound/blob/master/examples/Imperative.hs)).
* [A simple assembly language (version 2)](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/Assembly2.hs) (adapted from [a corresponding example from the Bound package](https://github.com/ekmett/bound/blob/master/examples/Imperative.hs)).
* [Style](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/Style.hs) discusses programming style, with examples of recommended practice, and of what to avoid.
* [An implementation of System F](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/SystemF.hs) is an illustrative example of those functions applied in something resembling typical practice.
* [An implementation of a EUTxO blockchain system](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/IdealisedEUTxO.hs) is another, quite different, example of those functions applied in something resembling typical practice.
* More examples are in preparation.


## Building and running

Clone this repo:

        $ git clone https://github.com/bellissimogiorno/nominal.git
        $ cd nominal

### Using `Stack`

1. Install [Stack](https://github.com/commercialhaskell/stack).


2. Build:

        $ stack build

3. Read the documentation:

        $ stack haddock --open

4. Run some unit- and property-based tests:

        $ stack test

5. Explore it in ghci:

        $ stack ghci src/Language/Nominal/Examples/SystemF.hs
        $ stack ghci src/Language/Nominal/Examples/IdealisedEUTxO.hs

### Using `Cabal`

1. Install [Cabal](https://www.haskell.org/cabal/).

2. Build:

        $ cabal build

3. Read the documentation:

        $ cabal haddock

   This will build the documentation and output the name of the `html`-file
   that you can then open in your browser.

4. Run some unit- and property-based tests:

        $ cabal test --test-show-detail=direct

5. Explore it in ghci:

        $ cabal repl Language/Nominal/Examples/SystemF.hs
        $ cabal repl Language/Nominal/Examples/IdealisedEUTxO.hs

## Example

Copied from [the untyped lambda calculus example](https://github.com/bellissimogiorno/nominal/blob/master/src/Language/Nominal/Examples/UntypedLambda.hs), and see [a corresponding example from the Bound package](https://hackage.haskell.org/package/bound).

```haskell
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
   sub v t = rewrite $ \case -- 'rewrite' comes from Scrap-Your-Boilerplate generics.  It goes automatically under the binder.
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
whnf (Lam b' :@ a) = whnf $ b' `conc` a  
whnf             e = e

-- | (\x x) y
example1 :: Exp
example1 = (\[x, y] -> lam x (V x) :@ V y) `genAppC` freshNames ["x", "y"] 
-- | y
example1whnf :: Exp
example1whnf = whnf example1

-- | (\x xy) x
example2 :: Exp
example2 = (\[x, y] -> lam x (V x :@ V y) :@ V x) `genAppC` freshNames ["x", "y"] 
-- | xy
example2whnf :: Exp
example2whnf = whnf example2
```

## Acknowledgements

Thanks to [Lars Brünjes](https://github.com/brunjlar/) for help, support, and code contributions.
