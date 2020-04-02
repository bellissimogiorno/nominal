{-|
Module      : Nominal 
Description : Implementation of nominal techniques as a Haskell package
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Nominal-flavoured implementation of data in a context of local names, designed following the ideas in <https://link.springer.com/article/10.1007/s001650200016 a new approach to abstract syntax with variable binding> (see also <http://www.gabbay.org.uk/papers.html#newaas-jv author's pdfs>).

See also:

- A tutorial in "Language.Nominal.Examples.Tutorial".
- An example development of System F in "Language.Nominal.Examples.SystemF".
- Properties in "Language.Nominal.Properties.AllTests".

-}

module Language.Nominal
     ( module Language.Nominal.Names
     , module Language.Nominal.Nom
     , module Language.Nominal.Sub
     , module Language.Nominal.Abs
     ) 
    where

import Language.Nominal.Names 
import Language.Nominal.Nom 
import Language.Nominal.Sub
import Language.Nominal.Abs 

