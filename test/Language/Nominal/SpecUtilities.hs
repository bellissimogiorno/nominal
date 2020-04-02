{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Nominal.SpecUtilities
    (
    ) where

import System.IO.Unsafe (unsafePerformIO)
import Data.Unique      (Unique, newUnique)

import Test.QuickCheck

import Language.Nominal.Names
import Language.Nominal.Nom
import Language.Nominal.Abs
import Language.Nominal.Examples.SystemF

myatomnames :: [String]
myatomnames = map show [0 :: Int .. 9]

myatoms :: [Atom]
myatoms = unsafePerformIO $ mapM (\_x -> Atom <$> newUnique) myatomnames 

-- | We only care about short and simple strings
instance {-# OVERLAPPING #-} Arbitrary String where
--   arbitrary = getPrintableString <$> arbitrary 
   arbitrary = elements $ map (\x -> [x]) (['a'..'z']++['A'..'Z'])

-- | Pick an atom
instance Arbitrary Atom where
   arbitrary = elements myatoms 

instance Arbitrary a => Arbitrary (Name a) where
   arbitrary = do -- Gen monad
      atm <- arbitrary  
      a <-   arbitrary  
      return $ Name (Just a, atm) 
instance {-# OVERLAPPING #-} Arbitrary (Name String) where
   arbitrary = do -- Gen monad
      atm <- arbitrary  
      return $ Name (Just (show atm), atm) 
{-- instance Arbitrary (Name ()) where
   arbitrary = do -- Gen monad
      a <- arbitrary 
      return $ Name (Just (), a) 
--}

instance (Swappable t a, Arbitrary (Name t), Arbitrary a) => Arbitrary (Abs t a) where
   arbitrary = do -- Gen monad
      nam <- arbitrary
      a   <- arbitrary
      return $ absByName nam a

instance (Swappable t a, Arbitrary (Name t), Arbitrary a) => Arbitrary (Nom t a) where
   arbitrary = do -- Gen monad
      nams <- arbitrary
      a   <- arbitrary
      return $ res nams a


-- | For QuickCheck tests: pick a type
instance Arbitrary Typ where
  arbitrary =
    sized arbitrarySizedTyp

arbitrarySizedTyp :: Int -> Gen Typ 
arbitrarySizedTyp m = 
  if m < 2 then 
     TVar <$> arbitrary 
  else do -- Gen monad
     oneof [TVar <$> arbitrary
           ,do -- Gen monad
               t1 <- arbitrarySizedTyp (m `div` 2) 
               t2 <- arbitrarySizedTyp (m `div` 2)
               return $ t1 :-> t2
           ,do -- Gen monad
               t <- arbitrarySizedTyp (m-1)
               n <- arbitrary
               return $ All (absByName n t)
           ]

-- | For QuickCheck tests: pick a term 
instance Arbitrary Trm where
  arbitrary =
    sized arbitrarySizedTrm

arbitrarySizedTrm :: Int -> Gen Trm 
arbitrarySizedTrm m = 
  if m < 2 then 
     Var <$> arbitrary 
  else do -- Gen monad
     oneof [Var <$> arbitrary
           ,do -- Gen monad
               t1 <- arbitrarySizedTrm (m `div` 2) 
               t2 <- arbitrarySizedTrm (m `div` 2)
               return $ App t1 t2
           ,do -- Gen monad
               t <- arbitrarySizedTrm (m-1)
               n <- arbitrary
               return $ Lam (absByName n t)
           ,do -- Gen monad
               t1 <- arbitrarySizedTrm (m `div` 2) 
               t2 <- arbitrarySizedTyp (m `div` 2)
               return $ TApp t1 t2
           ,do -- Gen monad
               t <- arbitrarySizedTrm (m-1)
               n <- arbitrary
               return $ TLam (absByName n t)
           ]

