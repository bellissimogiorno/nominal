{-|
Module      : Sub 
Description : Nominal treatment of substitution
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Typeclass for types that support a substitution action.  Capture-avoidance is automatic, provided you used @'Nom'@ or @'Abs'@ types for binding, of course.  

See "Language.Nominal.Examples.SystemF" for usage examples. 
-}

{-# LANGUAGE ConstraintKinds       
           , DataKinds             
           , DefaultSignatures     
           , DerivingVia           
           , EmptyCase             
           , FlexibleContexts      
           , FlexibleInstances     
           , InstanceSigs          
           , MultiParamTypeClasses 
           , PartialTypeSignatures   
           , PolyKinds               
           , StandaloneDeriving      
           , TupleSections         
           , TypeOperators         
#-}

module Language.Nominal.Sub
   ( -- * Substitution
     KSub (..)
   , Sub
   -- * Test
   -- $test
   ) 
    where

import GHC.Generics         
-- import Type.Reflection 
import Data.List.NonEmpty (NonEmpty)

import Language.Nominal.Name 

-- * Substitution

-- | Substitution.  @sub n x y@ corresponds to "substitute the name n for the datum x in y".
--
-- We intend that @n@ should be a type of names @KName k n@. 
class KSub n x y where
    sub :: n -> x -> y -> y
    -- We could reasonably insert a MINIMAL condition here, but in this case we don't because there's a default instance. 
    default sub :: (Generic y, GSub n x (Rep y)) => n -> x -> y -> y
    sub n x = to . gsub n x . from

-- | Canonical instance for the unit atom sort
type Sub n x y = KSub (KName 'Tom n) x y


-- order: nameless, tuple, list, nonempty list, maybe, sum, nom 

-- | sub on nameless type is trivial
instance KSub n x (Nameless a) where
   sub _ _ = id

deriving via Nameless Bool instance KSub n x Bool
deriving via Nameless Int instance KSub n x Int
deriving via Nameless () instance KSub n x ()
deriving via Nameless Char instance KSub n x Char

instance (KSub n x a, KSub n x b) => KSub n x (a, b)
instance (KSub n x a, KSub n x b, KSub n x c) => KSub n x (a, b, c)
instance (KSub n x a, KSub n x b, KSub n x c, KSub n x d) => KSub n x (a, b, c, d)
instance (KSub n x a, KSub n x b, KSub n x c, KSub n x d, KSub n x e) => KSub n x (a, b, c, d, e)
instance KSub n x a => KSub n x [a]
instance KSub n x a => KSub n x (NonEmpty a)
instance KSub n x a => KSub n x (Maybe a)
instance (KSub n x a, KSub n x b) => KSub n x (Either a b)


-- | sub on names
instance KSub (KName s n) (KName s n) (KName s n) where -- We could legitimately insist on Typeable (s :: k), KSwappable k n, Eq n here, but we do not because names are compared for equality by atom.
   sub n n' a = if a == n then n' else a 


-- * Generics support for @'KSub'@

class GSub n x f where
    gsub :: n -> x -> f w -> f w 

instance GSub n x V1 where
    gsub _ _ y = case y of

instance GSub n x U1 where
    gsub _ _ = id

instance GSub n x f => GSub n x (M1 i t f) where
    gsub n x = M1 . gsub n x . unM1

instance KSub n x c => GSub n x (K1 i c) where
    gsub n x = K1 . sub n x . unK1

instance (GSub n x f, GSub n x g) => GSub n x (f :*: g) where
    gsub n x (y :*: z) = gsub n x y :*: gsub n x z

instance (GSub n x f, GSub n x g) => GSub n x (f :+: g) where
    gsub n x (L1 y) = L1 $ gsub n x y
    gsub n x (R1 z) = R1 $ gsub n x z

{- $tests Property-based tests are in "Language.Nominal.Properties.SubSpec". -}
