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
           , StandaloneDeriving      
           , TupleSections         
           , TypeOperators         
#-}

{-# OPTIONS_GHC -fno-warn-orphans #-} -- Suppress orphan instance of BinderConc instance of KAbs.

module Language.Nominal.Sub
   ( -- * Substitution
     KSub (..)
   , Sub
   -- * Test
   -- $test
   ) 
    where

import GHC.Generics         
import Type.Reflection 
import Data.List.NonEmpty (NonEmpty)

import Language.Nominal.Name 
import Language.Nominal.Binder
import Language.Nominal.Abs

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
type Sub n x y = KSub (KName Tom n) x y


-- order: nameless, tuple, list, nonempty list, maybe, sum, nom 

-- | sub on nameless type is trivial
instance KSub n x (Nameless a) where
   sub _ _ = id

deriving via Nameless Bool instance KSub n x Bool
deriving via Nameless Int  instance KSub n x Int
deriving via Nameless ()   instance KSub n x ()
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
instance KSub (KName s n) (KName s n) (KName s n) where -- We could legitimately insist on Typeable s, Swappable n, Eq n here, but we do not because names are compared for equality by atom.
   sub n n' a = if a == n then n' else a 

-- | Nameless form of substitution, where the name for which we substitute is packaged in a @'KAbs'@ abstraction. 
instance {-# INCOHERENT #-} (Typeable s, Swappable n, Swappable x, Swappable y, KSub (KName s n) x y) => BinderConc (KAbs (KName s n) y) (KName s n) y s x where  -- may be overlapped by the native `conc` name instance of KAbs.  If in doubt, favour the native version.  This may change.
   conc y' x = y' @@! \n -> sub n x  
 

{-- | Nameless form of substitution, where the name for which we substitute is packaged in a @'KAbs'@ abstraction. 
subApp :: (Typeable s, Swappable n, Swappable x, Swappable y, KSub (KName s n) x y) => KAbs (KName s n) y -> x -> y
subApp y' x = y' @@! \n -> sub n x -- flip sub x 
-- | Nameless form of substitution, where the name for which we substitute is packaged in a @'KAbs'@ abstraction ('flip'ped version). 
appSub :: (Typeable s, Swappable n, Swappable x, Swappable y, KSub (KName s n) x y) => x -> KAbs (KName s n) y -> y
appSub = flip subApp --}


-- | sub on a nominal abstraction substitutes in the label, and substitutes capture-avoidingly in the body
instance (Typeable s, Typeable u, KSub (KName s n) x t, KSub (KName s n) x y, Swappable t, Swappable y) => 
            KSub (KName s n) x (KAbs (KName u t) y) where
  sub n x = genApp $ \n' y -> (sub n x <$> n') @> sub n x y 

-- | Placeholder for future development.  A general maths behind this definition is given in Section 8.1 of <https://dl.acm.org/doi/10.1145/2700819 Semantics Out Of Context> (<http://gabbay.org.uk/papers.html#semooc author's pdf>).
instance Eq n => KSub n ((n -> a) -> a) (n -> a) where
   sub n x ctx n' = if n' == n then x ctx else ctx n'
-- | Placeholder for future development.  A general maths behind this definition is given in Section 8.1 of <https://dl.acm.org/doi/10.1145/2700819 Definition 8.12 of Semantics Out Of Context> (<http://gabbay.org.uk/papers.html#semooc author's pdf>).
instance Eq n => KSub n ((n -> a) -> a) ((n -> a) -> a) where
   sub n x x' ctx = x' (sub n x ctx)

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
