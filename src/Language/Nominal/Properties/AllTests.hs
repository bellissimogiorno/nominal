{-|
Module      : Tests for nominal package 
Description : Implementation of nominal techniques as a Haskell package, tests 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Nominal-flavoured implementation of data in a context of local names, designed following the ideas in <https://link.springer.com/article/10.1007/s001650200016 a new approach to abstract syntax with variable binding> (see also <http://www.gabbay.org.uk/papers.html#newaas-jv author's pdfs>).

Run tests by 

- typing @stack ghci AllTests@ from the command line in the directory containing @AllTests.hs@, then typing @quickcheck prop_name@ from the Haskell prompt, or 
- by typing @stack test@ from the command line (e.g. in the root directory of this package). 

-}

-- {-# LANGUAGE TemplateHaskell       #-}  -- needed for QuickCheck test generation
{-# OPTIONS_GHC -Wno-unused-imports #-}  -- suppress warnings of unused imports; intended here

module Language.Nominal.Properties.AllTests
    where

import Language.Nominal.Name 
import Language.Nominal.Nom 
import Language.Nominal.Sub 
import Language.Nominal.Abs 
import Language.Nominal.Examples.SystemF  
import Language.Nominal.Properties.SpecUtilities  
import Language.Nominal.Properties.NameSpec 
import Language.Nominal.Properties.NomSpec 
import Language.Nominal.Properties.AbsSpec 
import Language.Nominal.Properties.Examples.SystemFSpec 

import Test.QuickCheck 
-- import Test.QuickCheck.All

{--------------------------
return []
runTests :: IO Bool
runTests = $quickCheckAll
-}
