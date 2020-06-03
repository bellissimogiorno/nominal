{-|
Module      : Name
Description : Nominal theory of names and swappings
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

The basic framework: a nominal theory of names and swappings
-}

{-# LANGUAGE ConstraintKinds            
           , DataKinds                  
           , DefaultSignatures          
           , DeriveAnyClass             
           , DeriveGeneric              
           , DerivingStrategies         
           , DerivingVia                
           , DeriveDataTypeable
           , DeriveFunctor                
           , DeriveFoldable               
           , DeriveTraversable            
           , EmptyCase                  
           , EmptyDataDeriving
           , FlexibleContexts           
           , FlexibleInstances          
           , GADTs                      
           , GeneralizedNewtypeDeriving   
           , InstanceSigs               
           , MultiParamTypeClasses      
           , PartialTypeSignatures        
           , ScopedTypeVariables        
           , StandaloneDeriving           
           , TupleSections              
#-}

module Language.Nominal.Name
    ( -- $setup
      -- * Atoms
      KAtom (..)
    , Atom
    , Tom -- (..)
    , atTom
    -- * Creating atoms
    , freshKAtomsIO 
    , freshAtomsIO
    , freshKAtomIO 
    , freshAtomIO
    -- * Atom swapping
    , Swappable (..)
    , swp 
    -- * Permutations
    , KPerm 
    , Perm
    , perm
    -- * Names
    , KName (..)
    , Name
    , withLabel 
    , withLabelOf
    , justALabel
    , justAnAtom
    -- * Name swapping
    , kswpN
    , swpN
    -- * Nameless types
    , Nameless (..)
    -- * Tests
    -- $tests
    ) 
    where

import           Data.Data                  hiding (typeRep, TypeRep)
import           Data.List.NonEmpty         (NonEmpty)
import           Data.Type.Equality         -- for testEquality
import qualified Data.Map                   as DM 
import qualified Data.Set                   as S 
import           GHC.Generics               hiding (Prefix)
import           Type.Reflection

import           Language.Nominal.Unique
import           Language.Nominal.Utilities


{- $setup
-} 

-- * Atoms

-- | An atom is a unique atomic token. 
--
-- The argument @s@ of 'KAtom' is part of facilities offered by this package for declaring types of atom @s@ ranging over kinds @k@.  For usage see 'Language.Nominal.Examples.SystemF.ATyp', and 'Language.Nominal.Examples.SystemF.ATrm' in "Language.Nominal.Examples.SystemF".
-- 
-- /If your development requires just a single type of atomic tokens, ignore 'KAtom' and use 'Atom'./ 
newtype KAtom s = Atom Unique
   deriving (Eq, Ord, Generic, Typeable, Data)

-- | We provide a stock datatype @'Tom'@. 
--
-- Using the @DataKinds@ package, this is then used to provide a stock type of atoms @'Atom'@. 
data Tom 
   deriving (Eq, Ord, Generic, Typeable, Data)

-- | A proxy element for sort @'Tom'@.  If we pass this, we tell the typechecker we are "at Tom".
atTom :: Proxy Tom
atTom = Proxy

-- | A distinguished type of atoms.
--
-- It is populated by @'Tom'@s (below), thus an element of @'Atom'@ is "a Tom".
--
-- We provide @'Atom'@ as primitive for convenience.  If you need more than one type of atom (e.g. term atoms and type atoms), look at 'KAtom'. 
type Atom = KAtom Tom

-- | Display an atom by showing (the hash of) its unique id. 
instance Show (KAtom s) where
   show (Atom a) = "_" ++ show (hashUnique a)

-- * Creating atoms

-- | Make a fresh atom for each element of some list (@a@ny list).  /If you just want one fresh atom, use e.g. @[()]@./
--
-- This is an IO action; when executed, fresh identifiers get generated.
freshKAtomsIO :: Traversable m => m a -> IO (m (KAtom s))
freshKAtomsIO = mapM (const $ Atom <$> newUnique) 

-- | Make a fresh atom at @'Tom'@ for each element of some list (@a@ny list).
freshAtomsIO :: Traversable m => m a -> IO (m Atom)
freshAtomsIO = freshKAtomsIO

-- | For convenience: generate a fresh katom
freshKAtomIO :: IO (KAtom s) 
freshKAtomIO = head <$> freshKAtomsIO [()]

-- | For convenience: generate a fresh atom
--
-- >>> a <- freshAtomIO 
-- >>> b <- freshAtomIO
-- >>> a == b
-- False 
freshAtomIO :: IO Atom 
freshAtomIO = head <$> freshAtomsIO [()]

-- * Atom swapping

-- | Types that admit a __swapping action__.  
--
-- A swapping @(a b)@ maps 
--
-- * @a@ to @b@ and 
-- * @b@ to @a@ and 
-- * any other @c@ to @c@.
--
-- Swappings are invertible, which allows them to commute through type-formers containing negative arities, e.g. the left-hand argument of function arrow.  Swappings always distribute:
--
-- > swp a b (x, y)       == (swp a b x, swp a b y)
-- > swp a b [x1, x2, x3] == [swp a b x1, swp a b x2, swp a b x3] 
-- > swp a b (f x)        == (swp a b f) (swp a b x)
-- > swp a b (abst n x)   == abst (swp a b n) (swp a b x)
-- > swp a b (res [n] x)  == res [swp a b n] (swp a b x)
-- > swp a b (Name t x)   == Name (swp a b t) (swp a b x)
--
-- __Technical note:__ The content of @Swappable a@ is that @a@ supports a swapping action by atoms of every @s@.  Everything else, e.g. 'Language.Nominal.Nameset.KSupport', just uses @s@.  So @k@ is a "world" of sorts of atoms, for a particular application.
-- This is invisible at our default world @'Tom'@ because @'Tom'@ has only one inhabitant, @''Tom'@.  See 'Language.Nominal.Examples.SystemF.ASort' and surrounding code for a more sophisticated atoms setup.
class Swappable a where  

   kswp :: Typeable s => KAtom s -> KAtom s -> a -> a        --  swap n and n' in a
   default kswp :: (Typeable s, Generic a, GSwappable (Rep a)) => KAtom s -> KAtom s -> a -> a
   kswp n n' = to . gswp n n' . from

-- | A @'Tom'@-swapping
swp :: Swappable a => Atom -> Atom -> a -> a
swp = kswp

-- Don't need () instance because captured by @'Nameless'@ instance Swappable a => Swappable ()
instance Swappable a => Swappable (Maybe a)
instance Swappable a => Swappable [a]
instance Swappable a => Swappable (NonEmpty a)
instance (Ord a, Swappable a) => Swappable (S.Set a) where
   kswp a1 a2 s = S.fromList $ kswp a1 a2 (S.toList s)  -- Ord a so we can use fromList
instance (Swappable a, Swappable b) => Swappable (a, b)
instance (Swappable a, Swappable b, Swappable c) => Swappable (a,b,c)
instance (Swappable a, Swappable b, Swappable c,  Swappable d) => Swappable (a,b,c,d)
instance (Swappable a, Swappable b, Swappable c,  Swappable d, Swappable e) => Swappable (a,b,c,d,e)
instance (Swappable a, Swappable b) => Swappable (Either a b)


-- | Swap distributes over function types, because functions inherit swapping action pointwise (also called the /conjugation action/)
instance (Swappable a, Swappable b) => Swappable (a -> b) where
   kswp a1 a2 f = kswp a1 a2 . f . kswp a1 a2 

-- | Swap distributes over map types. 
--
-- Note that maps store their keys ordered for quick lookup, so a swapping acting on a map is not a noop and can provoke reorderings.
instance (Swappable a, Swappable b, Ord a) => Swappable (DM.Map a b) where
    kswp n1 n2 m = DM.fromList $ kswp n1 n2 (DM.toList m)  -- This design treats a map explicitly as its graph (list of pairs).  Could also view it as a function, and consider implementing conjugation action using DM.map and/or DM.mapKeys  

-- | Base case for swapping: atoms acting on atoms.
instance Typeable s => Swappable (KAtom s) where    -- typeable constraint gives us type representatives which allows the runtime type equality test (technically: type representation equality test) below. 
    kswp (a1 :: KAtom t) (a2 :: KAtom t) (a :: KAtom s) = -- explicit type annotations for clarity here 
        case testEquality (typeRep :: TypeRep t) (typeRep :: TypeRep s) of  
            Nothing         -> a   -- are s and t are different types 
            Just Refl              -- are s and t the same type? 
                | a == a1   -> a2  
                | a == a2   -> a1  
                | otherwise -> a


-- * Permutations

-- | A permutation represented as a list of swappings (simple but inefficient).
type KPerm s = [(KAtom s, KAtom s)] 

-- | A permutation at @'Tom'@.
type Perm = KPerm Tom

-- | A permutation acts as a list of swappings
perm :: (Typeable s, Swappable a) => KPerm s -> a -> a          
perm = chain . map (uncurry kswp)  


-- * Names

-- | A name is a pair of 
--
-- * an atom, and 
-- * a label @t@. 
--
-- @t@ is intended to store semantic information about the atom.  For instance, if implementing a simply-typed lambda-calculus then @t@ might be a dataype of (object-level) types.
--
-- A similar effect could be achieved by maintaining a monadic lookup context relating atoms to their semantic information; the advantage of using a name is that this information is packaged up with the atom in a local datum of type @'Name'@. 
data KName s t = Name { nameLabel :: t, nameAtom :: KAtom s}
   deriving (Generic, Functor, Foldable, Traversable, Typeable, Data) 

-- | Swapping atoms in names distributes normally; so we swap in the semantic label and also in the name's atom identifier.  Operationally, it's just a tuple action:
-- 
-- > swp atm1 atm2 (Name t atm)  = Name (swp atm1 atm2 t) (swp atm1 atm2 atm)
instance (Typeable s, Swappable t) => Swappable (KName s t) 

-- | A @'Tom'@ instance of @'KName'@.
type Name = KName Tom 


-- | Names are equal when they refer to the same atom.
-- 
-- WARNING: Labels are not considered! 
-- In particular, @t@-names always have @'Eq'@, even if the type of labels @t@ does not.
instance Eq (KName s t) where
   n1 == n2 = nameAtom n1 == nameAtom n2 

-- | Names are leq when their atoms are leq.
--
-- WARNING: Labels are not considered! 
-- In particular, @t@-names are always ordered even if /labels/ @t@ are unordered. 
instance Ord (KName s t) where
   n1 `compare` n2 = nameAtom n1 `compare` nameAtom n2 

instance Show t => Show (KName s t) where
   show nam = show (nameLabel nam) ++ show (nameAtom nam)
instance {-# OVERLAPPING #-} Show (KName s ()) where
   show nam = "n" ++ show (nameAtom nam)


-- | As the name suggests: overwrite the name's label
withLabel :: KName s t -> t -> KName s t
n `withLabel` t = const t <$> n -- functorial action automatically derived 

-- | Overwrite the name's label.  Intended to be read infix as @n `withLabelOf n'@
withLabelOf :: KName s t -> KName s t -> KName s t
n `withLabelOf` n' = n `withLabel` (nameLabel n') 

-- | Name with @'undefined'@ atom, so really just a label.  Use with care!
justALabel :: t -> KName s t
justALabel = flip Name undefined

-- | Name with @'undefined'@ label, so really just an atom.  Use with care!
justAnAtom :: KAtom s -> KName s t
justAnAtom = Name undefined 


-- * Name swapping

-- | A name swap discards the names' labels and calls the atom-swap @'kswp'@.
kswpN :: (Typeable s, Swappable a) => KName s t -> KName s t -> a -> a
kswpN n n' = kswp (nameAtom n) (nameAtom n') 

-- | A name swap for a @'Tom'@-name.  Discards the names' labels and calls a @'Tom'@-atom swapping.
swpN :: Swappable a => Name t -> Name t -> a -> a
swpN = kswpN 


-- * Nameless types

-- | Some types, like @'Bool'@ and @'String'@, are @'Nameless'@.  E.g. if we have a truth-value, we know it doesn't have any names in it; we might have used names to calculate the truth-value, but the truth-value itself @'True'@ or @'False'@ is nameless. 
newtype Nameless a = Nameless {getNameless :: a}
    deriving (Show, Read, Eq, Ord)

instance Swappable (Nameless a) where
    kswp _ _ = id
-- TODO: KEquivar s (Nameless a) where
-- KEquivar s (Nameless a) where
--    kswp _ _ = id

-- deriving via is described in:
-- Deriving Via: or, How to Turn Hand-Written Instances into an Anti-Pattern
-- https://www.kosmikus.org/DerivingVia/deriving-via-paper.pdf

deriving via Nameless Bool instance Swappable Bool
deriving via Nameless Int  instance Swappable Int
deriving via Nameless ()   instance Swappable ()
deriving via Nameless Char instance Swappable Char

-- | A smallish nameless type
-- data Smallish = SmallA | SmallB | SmallC | SmallD | SmallE
-- deriving via Nameless Smallish instance Swappable Smallish 

-- * Generics support for @'KSwappable'@

class GSwappable f where
    gswp :: Typeable s => KAtom s -> KAtom s -> f x -> f x

instance GSwappable V1 where   -- empty types, no instances
    gswp _ _ x = case x of

instance GSwappable U1 where   -- one constructor, no arguments
    gswp _ _ U1 = U1

instance Swappable c => GSwappable (K1 i c) where  -- base case.  wrapper for all of some type c so we escape back out to swp.  
    gswp m n x = K1 $ kswp m n $ unK1 x

instance (GSwappable f, GSwappable g) => GSwappable ((:*:) f g) where  -- products
    gswp m n (x :*: y) = gswp m n x :*: gswp m n y

instance (GSwappable f, GSwappable g) => GSwappable ((:+:) f g) where  -- sums
    gswp m n (L1 x) = L1 $ gswp m n x
    gswp m n (R1 y) = R1 $ gswp m n y

instance GSwappable f => GSwappable (M1 i c f) where -- meta-information.  e.g. constructor names (like for generic show method), fixity information; all captured by M1 type.  this is transparent for swappings
    gswp m n = M1 . gswp m n . unM1

{- $tests Property-based tests are in "Language.Nominal.Properties.NameSpec". -}
