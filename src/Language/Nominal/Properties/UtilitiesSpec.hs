module Language.Nominal.Properties.UtilitiesSpec
    where

import Data.Data 

import Language.Nominal.Utilities
import Language.Nominal.Name
import Language.Nominal.Properties.SpecUtilities ()


-- | Find integers and increment them
superSucc :: Data x => x -> x
superSucc = rewrite $ Just . (succ :: Int -> Int) 

-- | Rewrite rewrites inside a @[Int]@ 
prop_test_rewrite1 :: [Int] -> Bool 
prop_test_rewrite1 x = superSucc x == fmap succ x

-- | Rewrite rewrites inside a list of 'Int'-labelled names
prop_test_rewrite2 :: [Name Int] -> Bool 
prop_test_rewrite2 x = superSucc x == fmap (fmap succ) x

