{-|
Module      : NameSet 
Description : Theory of support, apartness, and restriction 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Typeclasses and operations having to do with sets of names/atoms, namely: 

* 'Support', 
* 'apart'ness, and 
* 'restrict'ion.
-}

{-# LANGUAGE ConstraintKinds       
           , DataKinds             
           , DefaultSignatures     
           , DerivingVia           
           , EmptyCase             
           , FlexibleContexts      
           , FlexibleInstances     
           , GADTs                 
           , InstanceSigs          
           , MultiParamTypeClasses 
           , PartialTypeSignatures   
           , PolyKinds               
           , ScopedTypeVariables     
           , StandaloneDeriving      
           , TupleSections         
           , TypeOperators         
#-}  

module Language.Nominal.NameSet
    ( -- * Support and apartness
      KSupport (..)
    , Support
    , supp
    , kapart
    , apart
    -- * Identifying list elements by name or atom 
    , atomPoint
    , namePoint
    -- * Restriction
    , KRestrict (..) 
    , Restrict
    , restrictN
    -- * Tests
    -- $tests
    ) where

import           Data.Proxy                 (Proxy (..))
import           Data.Type.Equality
import           Data.List.NonEmpty         (NonEmpty)
import           Data.Set                   (Set)
import qualified Data.Set                   as S   
import           GHC.Generics          
import           Type.Reflection

import           Language.Nominal.Name
import           Language.Nominal.Utilities



-- * Support

-- | A typeclass for elements for which a supporting set of atoms can be computed in a structural, type-directed manner.  
--
-- So: /lists/ yes and /function-types/ no.  See instances for full details. 
--
class (Typeable s, KSwappable k a) => KSupport (s :: k) a where   
    ksupp :: proxy s -> a -> Set (KAtom s)
    default ksupp :: (Generic a, GSupport s (Rep a)) => proxy s -> a -> Set (KAtom s)
    ksupp _ = gsupp . from

-- | A ''Tom' instance of 'KSupport'. 
type Support a = KSupport 'Tom a

supp :: Support a => a -> Set Atom
supp = ksupp atTom

instance Typeable s => KSupport s (Nameless a) where
    ksupp _ _ = S.empty 
deriving via Nameless ()   instance Typeable s => KSupport s ()
deriving via Nameless Bool instance Typeable s => KSupport s Bool
deriving via Nameless Char instance Typeable s => KSupport s Char
deriving via Nameless Int  instance Typeable s => KSupport s Int

-- order: nameless, tuple, list, nonempty list, maybe, sum, atom, name, nom, abs 
instance (Typeable (s :: k), Typeable (t :: k)) => KSupport s (KAtom t) where  -- We need s and t to both have kind k so that testEquality will work.  testEquality can only compare two types of the same kind. 
    ksupp _ a = case testEquality (typeRep :: TypeRep s) (typeRep :: TypeRep t) of
        Nothing   -> S.empty
        Just Refl -> S.singleton a
instance (Typeable (s :: k), Typeable (u :: k), KSupport s t) => KSupport s (KName u t) where
   ksupp p a = (ksupp p $ nameAtom a) `S.union` (ksupp p $ nameLabel a) 
-- instance {-# OVERLAPPABLE #-} (Foldable f, KSupport s a) => KSupport s (f a) where
--    supp = foldMap supp -- No good: causes Ambiguity warnings; and incorrect on pairs, which are foldable but by action on second component.
instance KSupport s a => KSupport s (Maybe a)
instance KSupport s a => KSupport s [a]
instance KSupport s a => KSupport s (NonEmpty a)
instance (Ord a, KSupport s a) => KSupport s (S.Set a) where 
   ksupp p = foldMap $ ksupp p
instance (KSupport s a, KSupport s b) => KSupport s (a, b)
instance (KSupport s a, KSupport s b, KSupport s c) => KSupport s (a, b, c)
instance (KSupport s a, KSupport s b, KSupport s c, KSupport s d) => KSupport s (a, b, c, d)
instance (KSupport s a, KSupport s b, KSupport s c, KSupport s d, KSupport s e) => KSupport s (a, b, c, d, e)
instance (KSupport s a, KSupport s b) => KSupport s (Either a b)
-- TODO: map instance 

-- | @a@ and @b@ are 'kapart' when they are supported by disjoint sets of @s@-atoms.
--
-- /We use @proxy@ instead of 'Proxy' below, so the user can supply any type that mentions @s@./ 
kapart :: (KSupport s a, KSupport s b) => proxy s -> a -> b -> Bool  
kapart p a b = S.disjoint (ksupp p a) (ksupp p b)

-- | @a@ and @b@ are 'apart' when they are supported by disjoint sets of atoms.
apart :: (Support a, Support b) => a -> b -> Bool
apart = kapart atTom


-- * Identifying list elements by name or atom 

-- | Bring the first element of a list-like structure that an atom points to (by being mentioned in the support), and put it at the head of the nonempty list.  Raises error if no such element exists. 
atomPoint :: (Foldable f, KSupport s a) => KAtom s -> f a -> NonEmpty a
atomPoint a = point $ S.member a . ksupp Proxy

-- | `atomPoint`, for names.  A name is just a labelled atom, and @namePoint@ just discards the label and calls @'atomPoint'@.
namePoint :: (Foldable f, KSupport s a) => KName s t -> f a -> NonEmpty a
namePoint = atomPoint . nameAtom


-- * Restriction

-- | Class for types that support a /remove these atoms from my support, please/ operation. 
-- Should satisfy e.g.: 
--  
-- > restrict atms $ restrict atms x == restrict atms x
--
-- > atms `apart` x ==> restrict atms x == x
--
-- The canonical instance of @'KRestrict'@ is @'Language.Nominal.Nom.Nom'@.
-- The @'KSwappable'@ constraint is not necessary for the code to run, but in practice wherever we use @'KRestrict'@ we expect the type to have a swapping action.
--
-- /Note for experts:/ We may want @'KRestrict'@ without @'KSupport'@, for example to work with @Nom (Atom -> Atom)@. 
--
-- /Note for experts:/ Restriction is familiar in general terms (e.g. pi-calculus restriction).  In a nominal context, the original paper is <https://dl.acm.org/doi/10.1145/1069774.1069779 nominal rewriting with name-generation> (<http://gabbay.org.uk/papers.html#nomrng author's pdf>), and this has a for-us highly pertinent emphasis on unification and rewriting. 
class (Typeable s, KSwappable k a) => KRestrict (s :: k) a where
   restrict  :: [KAtom s] -> a -> a   

-- | Instance of 'KRestrict' on a ''Tom'.
type Restrict = KRestrict 'Tom

-- | Form of restriction that takes names instead of atoms.  Just discards name labels and calls @'restrict'@.
restrictN :: KRestrict s a => [KName s t] -> a -> a
restrictN l = restrict (nameAtom <$> l)


-- | Restriction is trivial on elements of nameless types 
instance Typeable s => KRestrict s (Nameless a) where
   restrict _ = id

deriving via Nameless Bool instance Typeable s => KRestrict s Bool
deriving via Nameless Int instance Typeable s => KRestrict s Int
deriving via Nameless () instance Typeable s => KRestrict s ()
deriving via Nameless Char instance Typeable s => KRestrict s Char

-- | Restriction is monadic on Maybe 
instance (Typeable s, KRestrict s a) => KRestrict s (Maybe a) where
  restrict atms a = restrict atms <$> a
-- | On lists, Restrict traverses the list and eliminate elements for which any of the @atms@ are in the support.  
--
-- A alternative is to assume restriction on the underlying elements and restrict pointwise.  The elimination choice seems more useful in practice. 
instance (Typeable s, KSupport s a) => KRestrict s [a] where
   restrict atms as = filter (kapart (Proxy :: Proxy s) atms) as
-- | Eliminate elements for which any of the @atms@ are in the support
instance (Typeable s, Ord a, KSupport s a) => KRestrict s (S.Set a) where
   restrict atms as = S.filter (kapart (Proxy :: Proxy s) atms) as



-- * Generics support for @'KSupport'@
--
class GSupport s f where
    gsupp :: f x -> Set (KAtom s)

instance GSupport s V1 where
    gsupp x = case x of

instance GSupport s U1 where
    gsupp U1 = S.empty

instance GSupport s f => GSupport s (M1 i t f) where
    gsupp = gsupp . unM1

instance KSupport s c => GSupport s (K1 i c) where
    gsupp = ksupp Proxy . unK1

instance (GSupport s f, GSupport s g) => GSupport s (f :*: g) where
    gsupp (x :*: y) = gsupp x `S.union` gsupp y

instance (GSupport s f, GSupport s g) => GSupport s (f :+: g) where
    gsupp (L1 x) = gsupp x
    gsupp (R1 y) = gsupp y

{- $tests Property-based tests are in "Language.Nominal.Properties.NameSetSpec". -}
