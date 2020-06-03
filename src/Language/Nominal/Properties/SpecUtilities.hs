{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Nominal.Properties.SpecUtilities
    where

import qualified Data.List.NonEmpty                as NE
import           Data.Proxy                        (Proxy (..))
import           System.IO.Unsafe                  (unsafePerformIO)
import           Type.Reflection                   (Typeable)

import           Test.QuickCheck

import           Language.Nominal.Abs
import           Language.Nominal.Examples.SystemF
import           Language.Nominal.Name
import           Language.Nominal.Nom
import           Language.Nominal.Binder
import           Language.Nominal.Unify
import           Language.Nominal.Unique
import           Language.Nominal.Equivar

myatomnames :: [String]
myatomnames = map show [0 :: Int .. 25]

{-# NOINLINE myUniques #-}  -- play safe because of unsafePerformIO
myUniques :: [Unique]
myUniques = unsafePerformIO $ mapM (\_x -> newUnique) myatomnames 

myAtoms :: proxy s -> [KAtom s]
myAtoms _ = Atom <$> myUniques

-- | We only care about short and simple strings
instance {-# OVERLAPPING #-} Arbitrary String where
    arbitrary = elements $ map return (['a'..'z']++['A'..'Z'])

-- | Pick an atom
instance Arbitrary (KAtom s) where
    arbitrary = elements $ myAtoms (Proxy :: Proxy s)

instance Arbitrary a => Arbitrary (KName s a) where
   arbitrary = Name <$> arbitrary <*> arbitrary
instance {-# OVERLAPPING #-} Arbitrary (Name String) where
   arbitrary = do -- Gen monad
      atm <- arbitrary  
      return $ Name (show atm) atm

instance (Typeable s, Swappable t, Swappable a, Arbitrary (KName s t), Arbitrary a) => Arbitrary (KAbs (KName s t) a) where
   arbitrary = do -- Gen monad
      nam <- arbitrary
      a   <- arbitrary
      return $ nam @> a  -- hlint suggestion ignored

instance (Typeable s, Swappable a, Arbitrary a) => Arbitrary (KNom s a) where
   arbitrary = do -- Gen monad
      nams <- arbitrary
      a    <- arbitrary
      return $ nams @> a   -- hlint suggestion ignored

-- | For QuickCheck tests: pick a type
instance Arbitrary Typ where
  arbitrary =
    sized arbitrarySizedTyp

arbitrarySizedTyp :: Int -> Gen Typ 
arbitrarySizedTyp m = 
  if m < 2 then 
     TVar <$> arbitrary 
  else 
     oneof [TVar <$> arbitrary
           ,do -- Gen monad
               t1 <- arbitrarySizedTyp (m `div` 2) 
               t2 <- arbitrarySizedTyp (m `div` 2)
               return $ t1 :-> t2
           ,do -- Gen monad
               t <- arbitrarySizedTyp (m-1)
               n <- arbitrary
               return $ All (n @> t)
           ]

-- | For QuickCheck tests: pick a term 
instance Arbitrary Trm where
  arbitrary =
    sized arbitrarySizedTrm

arbitrarySizedTrm :: Int -> Gen Trm 
arbitrarySizedTrm m = 
  if m < 2 then 
     Var <$> arbitrary 
  else 
     oneof [Var <$> arbitrary
           ,do -- Gen monad
               t1 <- arbitrarySizedTrm (m `div` 2) 
               t2 <- arbitrarySizedTrm (m `div` 2)
               return $ App t1 t2
           ,do -- Gen monad
               t <- arbitrarySizedTrm (m-1)
               n <- arbitrary
               return $ Lam (n @> t)
           ,do -- Gen monad
               t1 <- arbitrarySizedTrm (m `div` 2) 
               t2 <- arbitrarySizedTyp (m `div` 2)
               return $ TApp t1 t2
           ,do -- Gen monad
               t <- arbitrarySizedTrm (m-1)
               n <- arbitrary
               return $ TLam (n @> t)
           ]

instance Arbitrary a => Arbitrary (NE.NonEmpty a) where
    arbitrary = (NE.:|) <$> arbitrary <*> arbitrary

genEvFinMap :: (UnifyPerm a, Eq a, Eq b) => Gen a -> Gen b -> Gen (EvFinMap a b)
genEvFinMap genA genB = evFinMap <$> genB <*> listOf ((,) <$> genA <*> genB)

instance forall a b. 
         ( Arbitrary a
         , UnifyPerm a
         , Eq a
         , Arbitrary b
         , Eq b
         ) => Arbitrary (EvFinMap a b) where
    arbitrary = genEvFinMap arbitrary arbitrary
    shrink f = [evFinMap b xs | (b, xs) <- shrink $ fromEvFinMap f]
