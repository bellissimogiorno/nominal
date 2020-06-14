{-|
Module      : Unify 
Description : Unification by permutation
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Unification by permutation
-}

{-# LANGUAGE ConstraintKinds            
           , DataKinds                  
           , DefaultSignatures          
           , DeriveGeneric              
           , DerivingStrategies         
           , DerivingVia                
           , EmptyCase                  
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
           , TypeOperators              
#-}

module Language.Nominal.Unify
    ( -- $setup
      -- * Introduction
      -- -- $intro
      -- * @'Ren'@
      KRen (..)
    , Ren 
    , idRen
    , nothingRen
    , isJustRen 
    , isNothingRen 
      -- Manipulating renamings
    , renNub 
    , renExtend
    , renToList
    , renFromList
    , renRemoveBlock
      -- * Unification up to a @'KRen'@
    , KUnifyPerm (..)
    , UnifyPerm
    , unifyPerm
    , kunifiablePerm
    , unifiablePerm
      -- * Special case: unifying prefixes of lists
    , kevPrefixRen
    , evPrefixRen
    , kevIsPrefix
    , evIsPrefix
      -- * Tests
      -- $tests
    ) where

import           Data.Function            (on)
import qualified Data.Map.Strict          as DM -- for unifyPerm 
import           Data.Maybe               -- (isJust)
import           Data.List.Extra          (takeEnd)
import           Data.List.NonEmpty       (NonEmpty)
import           Data.Proxy               (Proxy (..))
import qualified Data.Set                 as S -- (fromList) 
import           Data.Type.Equality
import           GHC.Generics
import           Type.Reflection

import           Language.Nominal.Name
import           Language.Nominal.NameSet
import           Language.Nominal.Nom
import           Language.Nominal.Binder
import           Language.Nominal.Abs

-- $setup
-- >>> import Data.Set as S

{- $intro

-}


-- * @'Ren'@

-- | An element of `Ren` is either
-- 
-- 1. `Just` an injective finite map from `Atom` to `Atom` (for this file, call this a __renaming__), or
--
-- 2. A "nomap" value (`Nothing`).
-- 
-- A `Ren` represents a solution to the problem 
--
-- /does there exist a permutation that makes @x@ equal to @y@?/
--
-- A type in the @'KUnifyPerm'@ typeclass is structurally guaranteed to give /at most one/ solution to such a unification problem, up to renaming irrelevant atoms. 
-- So in a nutshell: names, lists, and tuples are good here, and functions (not an equality type) and sets (may have multiple solutions) are not good.
--
--  A 'Just' value represents a solution to this unification problem; a 'Nothing' value represents that no such solution can be found.  @'unifyPerm'@ calculates these solutions. 
newtype KRen s = Ren {unRen :: Maybe (DM.Map (KAtom s) (KAtom s))}
   deriving (Show, Generic)

instance Typeable s => Swappable (KRen s) where 
 
-- | Renaming on a @'Tom'@ instance
type Ren = KRen Tom

-- | The identity renaming.  
idRen :: KRen s 
idRen = Ren . Just $ DM.empty

-- | The Nothing renaming.  If we think of @'KRen' s@ as type of solutions to permutation unification problems, then @'nothingRen'@ indicates no solution could be found. 
nothingRen :: KRen s 
nothingRen = Ren Nothing 


-- | Is it Just a renaming?  (My unification problem can be solved, and here's the solution.) 
isJustRen :: KRen s -> Bool
isJustRen (Ren x) = isJust x

-- | Is it Nothing?  (Nope; no solution exists.) 
isNothingRen :: KRen s -> Bool
isNothingRen = not . isJustRen

-- | Elements of @'KRen'@ are compared for equality on their __nub__ @'renNub'@, meaning just that identity mappings are ignored.
--
-- >>> a = genUnNom $ freshAtom
-- >>> idRen == renExtend a a idRen
-- True 
instance Eq (KRen s) where
    (==) = (==) `on` (unRen . renNub)

-- | Elements of @'KRen'@ are compared on their __nub__ @'renNub'@, meaning just that identity mappings are ignored.
instance Ord (KRen s) where
    compare = compare `on` unRen . renNub

-- | Support of a renaming is the set of nontrivially mapped atoms 
--
-- >>> (supp (idRen :: Ren)) == S.empty
-- True
-- >>> (supp (nothingRen :: Ren)) == S.empty
-- True
instance Typeable s => KSupport s (KRen s) where
   ksupp _ (Ren m') = 
      fromMaybe S.empty $ 
         DM.foldrWithKey (\a b s -> if a == b then s else s `S.union` (S.fromList [a,b])) S.empty <$> m' 


-- | The parts of the map that are not identity
renNub :: KRen s -> KRen s
renNub (Ren m') = Ren $ DM.filterWithKey (/=) <$> m' 


-- | Extend a renaming m with a new pair a -> b, maintaining the property of being a partial injection.
-- If adding a->b would destroy partial injectivity, then return @Nothing@. 
renExtend :: KAtom s -> KAtom s -> KRen s -> KRen s
renExtend a b (Ren m') = Ren $ do -- Maybe monad 
   m <- m'
   case DM.lookup a m of
      Nothing | not $ elem b $ DM.elems m -> DM.insert a b <$> m' -- if a doesn't map and b isn't already mapped to, then add (a,b)
      Just b' | b' == b                   -> m' -- if a maps to b already, then do nothing 
      _                                   -> Nothing -- otherwise, complain

-- | Extract the graph of a 'Ren', Maybe.
renToList :: KRen s -> Maybe [(KAtom s, KAtom s)]
renToList (Ren Nothing)  = Nothing
renToList (Ren (Just m)) = Just $ DM.toList m

-- | Convert a graph to a 'Ren'. 
renFromList :: [(KAtom s, KAtom s)] -> KRen s
renFromList = foldr (\(a,b) r -> renExtend a b r) idRen 

-- | Given a block of atoms, remove them from the map /provided/ that the atoms in that block only map to other atoms within it; if an atom gets mapped across the block boundary, return @Nothing@. 
--
-- Needed for equality instance of 'Language.Nominal.Examples.IdealisedEUTxO.Chunk'.
renRemoveBlock :: [KAtom s] -> KRen s -> KRen s
renRemoveBlock _    (Ren Nothing)  = Ren Nothing
renRemoveBlock atms (Ren (Just m)) =
   DM.foldrWithKey (\a b r -> case (a `elem` atms, b `elem` atms) of  
                                 (True,  True)  -> r                 -- both elements in block; discard
                                 (False, False) -> renExtend a b r   -- both elements out of block; append (some inefficiency here, no doubt)
                                 _              -> nothingRen        -- otherwise stop
                   ) idRen m
              

instance Semigroup (KRen s) where
    (Ren (Just m)) <> r = DM.foldrWithKey renExtend r m 
    (Ren Nothing)  <> _ = Ren Nothing 

instance Monoid (KRen s) where
   mempty = Ren $ Just DM.empty

-- | There are two reasonable notions of restriction; filter, or default to Nothing.  We choose the option that discards minimal information, i.e. the filter.
instance Typeable s => KRestrict s (KRen s) where
   restrict :: [KAtom s] -> KRen s -> KRen s
   restrict as (Ren m') = Ren $ do -- Maybe monad
      m <- m'
      return $ DM.filterWithKey (\a b -> not (elem a as) && not (elem b as)) m

-- * Unification up to a @'KRen'@

-- | Equal-up-to-permutation.  The algorithm works very simply by traversing the element looking for atoms and when it finds them, trying to match them up.  If it can do so injectively then it succeeds with @'Just'@ a renaming; if it fails it returns @'Nothing'@. 
--
-- /Question: Granted that 'KUnifyPerm' is a subset of 'KSupport', why are they not equal?/
-- Because for simplicity we only consider types for which at most one unifier can be found, by an efficient structural traversal.
-- This avoids backtracking, and makes a 'kunifyPerm' a function to 'KRen'.
-- So, a key difference is that 'KSupport' can easily calculate the support of a set (unordered list without multiplicities) whereas 'KUnifyPerm' does not even attempt to calculate unifiers of sets; not because this would be impossible, but because it would require a significant leap in complexity that we do not seem to need (so far).
class KSupport s a => KUnifyPerm s a where
    
    -- | This calculates a solution to a unification problem
    kunifyPerm :: proxy s -> a -> a -> KRen s
    default kunifyPerm :: (Generic a, GUnifyPerm s (Rep a)) => proxy s -> a -> a -> KRen s
    kunifyPerm _ x y = gunifyPerm (from x) (from y)
   
    -- | This applies a solution to a unification problem (represented as a renaming) to an element.  
    --
    -- __Note:__ @'ren'@ is not just swapping.  It traverses the structure of its argument performing an atom-for-atom renaming.  In the case that its argument solves a unification problem, its /effect/ is the same as if a permuatation were applied.
    --
    -- This is checked in 'Language.Nominal.Properties.UnifySpec.iprop_fresh_ren' and 'Language.Nominal.Properties.UnifySpec.prop_unify_ren'.
    ren :: KRen s -> a -> a 
    default ren :: (Generic a, GUnifyPerm s (Rep a)) => KRen s -> a -> a
    ren r = to . gren r . from

-- | 'Tom'-instance of typeclass 'KUnifyPerm'.
type UnifyPerm = KUnifyPerm Tom

-- | Unify on 'Atom's, thus 'Tom'-instance of 'kunifyPerm'.
unifyPerm :: UnifyPerm a => a -> a -> Ren
unifyPerm = kunifyPerm atTom

-- | Does an s-unifier exist?
--
-- We write @proxy@ instead of 'Proxy' for the user's convenience, so the user can take advantage of any type that mentions @s@.
kunifiablePerm :: KUnifyPerm s a => proxy s -> a -> a -> Bool 
kunifiablePerm p a a' = isJustRen $ kunifyPerm p a a' 

-- | Does a 'Tom'-unifier exist?
unifiablePerm :: UnifyPerm a => a -> a -> Bool
unifiablePerm = kunifiablePerm atTom


----------------------------------------------
-- KUnifyPerm instances
-- instance order: nameless, tuple, list, nonempty list, maybe, sum, atom, name, nom, abs 

instance (Typeable s, Eq a) => KUnifyPerm s (Nameless a) where
    kunifyPerm _ a b
        | a == b    = mempty
        | otherwise = Ren Nothing
    ren _ = id

deriving via Nameless Bool instance Typeable s => KUnifyPerm s Bool
deriving via Nameless Int  instance Typeable s => KUnifyPerm s Int
deriving via Nameless ()   instance Typeable s => KUnifyPerm s ()
deriving via Nameless Char instance Typeable s => KUnifyPerm s Char

instance (KUnifyPerm s a, KUnifyPerm s b) => KUnifyPerm s (a, b)
instance (KUnifyPerm s a, KUnifyPerm s b, KUnifyPerm s c) => KUnifyPerm s (a, b, c)
instance (KUnifyPerm s a, KUnifyPerm s b, KUnifyPerm s c, KUnifyPerm s d) => KUnifyPerm s (a, b, c, d)
instance (KUnifyPerm s a, KUnifyPerm s b, KUnifyPerm s c, KUnifyPerm s d, KUnifyPerm s e) => KUnifyPerm s (a, b, c, d, e)
instance KUnifyPerm s a => KUnifyPerm s [a]
instance KUnifyPerm s a => KUnifyPerm s (NonEmpty a)
instance KUnifyPerm s a => KUnifyPerm s (Maybe a)
instance (KUnifyPerm s a, KUnifyPerm s b) => KUnifyPerm s (Either a b)

-- | Unify atoms
instance (Typeable s, Typeable t) => KUnifyPerm s (KAtom t) where

    kunifyPerm :: proxy s -> KAtom t -> KAtom t -> KRen s
    kunifyPerm _ a b = case testEquality (typeRep :: TypeRep s) (typeRep :: TypeRep t) of
        Nothing
            | a == b    -> mempty
            | otherwise -> Ren Nothing
        Just Refl       -> renExtend a b mempty

    ren :: KRen s -> KAtom t -> KAtom t
    ren (Ren (Just m)) a =
        case testEquality (typeRep :: TypeRep s) (typeRep :: TypeRep t) of
            Nothing   -> a
            Just Refl -> DM.findWithDefault a a m
    ren (Ren Nothing)  a = a

-- | Unify names: they behave just an atom-label tuple  
instance (Typeable s, Typeable u, KUnifyPerm s t) => KUnifyPerm s (KName u t)

-- | Unify 'Nom' abstractions.
-- Unpack, unify, clean out fresh names
instance (Typeable s, KUnifyPerm s a) => KUnifyPerm s (KNom s a) where
   -- kunifyPerm p noma nomb = resAppC (\a -> resAppC (kunifyPerm p a) nomb) noma  
   kunifyPerm p noma nomb = resAppC' noma $ \a -> resAppC' nomb $ \b -> kunifyPerm p a b
   ren r m = ren r <$> m


-- | Unify 'Abs' name-abstraction
instance (Typeable s, KUnifyPerm s t, KUnifyPerm s a) => KUnifyPerm s (KAbs (KName s t) a) where
   kunifyPerm p absa absb = 
      (fuse (absa, absb)) @@. \na (a,b) -> kunifyPerm p (na, a) (na, b) -- use of '@@.' here cleans out the (na, na) binding. 
   ren r m = ren r <$> m


-- * Special case: unifying prefixes of lists

-- | Unify a list with a prefix of the other 
kevPrefixRen :: KUnifyPerm s a => proxy s -> [a] -> [a] -> KRen s
kevPrefixRen p l1 l2 = kunifyPerm p l1 (takeEnd (length l1) l2)

-- | Unify a list with a prefix of the other (at @'Tom'@ version). 
evPrefixRen :: UnifyPerm a => [a] -> [a] -> Ren
evPrefixRen = kevPrefixRen atTom


-- | One list unifies with a prefix of the other 
kevIsPrefix :: forall s proxy a. KUnifyPerm s a => proxy s -> [a] -> [a] -> Bool 
kevIsPrefix p l1 l2 = isJustRen $ kevPrefixRen p l1 l2

-- | One list unifies with a prefix of the other (at @'Tom'@ version). 
evIsPrefix :: UnifyPerm a => [a] -> [a] -> Bool  
evIsPrefix = kevIsPrefix atTom


-- * Generics support for @'KUnifyPerm'@

class GUnifyPerm s f where
    gunifyPerm :: f x -> f x -> KRen s
    gren       :: KRen s -> f x -> f x

instance GUnifyPerm s V1 where
    gunifyPerm x = case x of
    gren _ x = case x of

instance GUnifyPerm s U1 where
    gunifyPerm U1 U1 = mempty
    gren _ U1 = U1

instance (GUnifyPerm s f, GUnifyPerm s g) => GUnifyPerm s (f :*: g) where
    gunifyPerm (x1 :*: y1) (x2 :*: y2) = gunifyPerm x1 x2 <> gunifyPerm y1 y2
    gren r (x :*: y) = gren r x :*: gren r y

instance (GUnifyPerm s f, GUnifyPerm s g) => GUnifyPerm s (f :+: g) where

    gunifyPerm (L1 x) (L1 y) = gunifyPerm x y
    gunifyPerm (R1 x) (R1 y) = gunifyPerm x y
    gunifyPerm _      _      = Ren Nothing

    gren r (L1 x) = L1 $ gren r x
    gren r (R1 x) = R1 $ gren r x

instance KUnifyPerm s c => GUnifyPerm s (K1 i c) where
    gunifyPerm (K1 x) (K1 y) = kunifyPerm Proxy x y    
    gren r (K1 x) = K1 $ ren r x

instance GUnifyPerm s f => GUnifyPerm s (M1 i t f) where
    gunifyPerm (M1 x) (M1 y) = gunifyPerm x y
    gren r (M1 x) = M1 $ gren r x

{- $tests Property-based tests are in "Language.Nominal.Properties.UnifySpec". -}

