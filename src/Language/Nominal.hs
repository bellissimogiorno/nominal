{-|
Module      : Nominal 
Description : Implementation of nominal techniques as a Haskell package
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Nominal-flavoured implementation of data in a context of local names, designed following the ideas in <https://link.springer.com/article/10.1007/s001650200016 a new approach to abstract syntax with variable binding> (see also <http://www.gabbay.org.uk/papers.html#newaas-jv author's pdfs>).

-}

{-# LANGUAGE CPP #-}

module Language.Nominal
     ( 
-- * Introduction
-- $blurb

-- * Quick links
-- $quicklinks

-- * Type(class) overview 
-- $quickref

       module Language.Nominal.Name
     , module Language.Nominal.NameSet
     , module Language.Nominal.Sub
     , module Language.Nominal.Nom
     , module Language.Nominal.Binder
     , module Language.Nominal.Abs
     , module Language.Nominal.Equivar
     , module Language.Nominal.Unify
     ) 
    where

import Language.Nominal.Name
import Language.Nominal.NameSet
import Language.Nominal.Sub
import Language.Nominal.Nom 
import Language.Nominal.Binder
import Language.Nominal.Abs 
import Language.Nominal.Equivar
import Language.Nominal.Unify

#include "Nominal/Blurb.txt"

{- $quicklinks

== Worked examples 

* "Language.Nominal.Examples.Tutorial": We explore some basic concepts. 
* "Language.Nominal.Examples.UntypedLambda": Untyped lambda-calculus syntax and reductions (short example). 
* "Language.Nominal.Examples.Assembly1": A simple assembly language, with binding (short example). 
* "Language.Nominal.Examples.Assembly2": A simple assembly language, with binding and a swap-variable primitive (short example). 
* "Language.Nominal.Examples.Style": Some basic comments on recommended programming style using this package. 
* "Language.Nominal.Examples.SystemF": System F syntax and reductions (longer example). 
* "Language.Nominal.Examples.IdealisedEUTxO": A EUTxO-style blockchain system, following the ideas in <https://arxiv.org/abs/2003.14271 mathematical idealisation of the Extended UTxO model> (longer example). 

== Links and references

* This package's <https://github.com/bellissimogiorno/nominal GitHub page>.
* The underlying mathematical model is described in <https://link.springer.com/article/10.1007/s001650200016 a new approach to abstract syntax with variable binding> (<http://www.gabbay.org.uk/papers.html#newaas-jv author's pdfs>).
* The paper on <https://arxiv.org/abs/1009.2791v1 closed nominal rewriting> (<http://www.gabbay.org.uk/papers.html#clonre author's pdfs>) is pertinent to the design of "Language.Nominal.Unify".
* The paper on the <https://arxiv.org/abs/2003.14271 mathematical idealisation of the Extended UTxO model> is pertinent "Language.Nominal.Examples.IdealisedEUTxO".
* This draft book on <https://www.mimuw.edu.pl/~bojan/upload/main-10.pdf orbit-finite sets> may be of interest.
* The <https://hackage.haskell.org/package/bound Bound package>, from which the worked examples "Language.Nominal.Examples.Assembly1" and "Language.Nominal.Examples.Assembly2" are adapted. 

== Related work 
* <https://hackage.haskell.org/package/bound bound: Making de Bruijn Succ less>
* <https://hackage.haskell.org/package/unbound unbound: Generic support for programming with names and binders>
* <https://hackage.haskell.org/package/unbound-generics unbound-generics: Support for programming with names and binders using GHC Generics>
* <https://hackage.haskell.org/package/nominal nominal: Binders and alpha-equivalence made easy> 
* <https://www.mimuw.edu.pl/~szynwelski/nlambda/doc/ NLambda: computations over infinite structures using logical formulas and SMT solving>

/(Something I should put on this list?  Let me know.)/
-}

{- $quickref

Here is an overview of some core typeclasses:

* 'Language.Nominal.Name.KAtom' and 'Language.Nominal.Name.Atom': 
Types of atomic freshly generatable identifiers. 
* 'Language.Nominal.Name.KName' and 'Language.Nominal.Name.Name': 
Types of labelled atoms.
* 'Language.Nominal.Name.KSwappable' and 'Language.Nominal.Name.Swappable':  
Typeclasses of types with a /swapping action/ by atoms and names.
* 'Language.Nominal.Name.KSupport' and 'Language.Nominal.Name.Support':  
Typeclasses of types with a structural notion of /the atoms in this object/.  In the mathematics, "support" coincides with "atoms for which the object may be asymmetric under swappings", but in this package support means something much stricter: that it is possible to traverse the data and pick out the atoms in its support.
/Note:/ "having empty support" does /not/ mean "having no atoms".  It means "symmetric under swapping atoms", which is not at all the same idea. 
* 'Language.Nominal.Name.Nameless': types like @Int@, @String@, and @()@ that are guaranteed atoms-free. 
* 'Language.Nominal.Nom.KNom' and 'Language.Nominal.Nom.Nom': An atoms-binding monad.
* 'Language.Nominal.Binder.Binder': A typeclass for functions acting on binding types.
* 'Language.Nominal.Abs.KAbs' and 'Language.Nominal.Abs.Abs': A name-abstracting functor.
* 'Language.Nominal.Name.KRestrict' and 'Language.Nominal.Name.Restrict': A typeclass of types with an inherent notion of atoms-binding.
* 'Language.Nominal.Unify.KUnifyPerm' and 'Language.Nominal.Unify.UnifyPerm': Typeclasses of types with a notion of unification by injective partial functions on atoms.


-}

