{-|
Module      : Equivar 
Description : Theory of equivariant orbit-finite structures
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

This module contains functions for manipulating lists of representatives which represent orbit-finite equivariant maps, and applying them to arguments by matching representatives to arguments up to a swapping (permutation) action.
-}

{-# LANGUAGE ConstraintKinds       
           , DataKinds             
           , DeriveGeneric         
           , DeriveAnyClass        
           , FlexibleContexts      
           , FlexibleInstances     
           , GADTs                
           , InstanceSigs          
           , MultiParamTypeClasses 
           , PartialTypeSignatures 
           , PolyKinds             
           , ScopedTypeVariables   
           , TypeOperators         
#-}

module Language.Nominal.Equivar
   (
    -- * Equivariance 
    -- $intro
      KEvFun (..)
    , EvFun
    -- * Equivariant lists and maps
    -- $basiclists
    , kevRep
    , evRep
    , kevNub
    , evNub
    -- * Lookup 
    -- $lookup
    , kevLookup
    , evLookup
    , kevLookupList'
    , kevLookupList
    , evLookupList
    -- * Orbit-finite equivariant maps
    -- $orbitfinite
    , KEvFinMap
    , EvFinMap
    , ($$)
    , constEvFinMap
    , extEvFinMap
    , evFinMap
    , fromEvFinMap
    -- * Tests
    -- $tests
    ) where

import qualified Data.Map.Strict          as DM -- for unifyPerm 
-- import           Data.Maybe               (fromMaybe)
import           Data.List                as L
import           Data.Proxy               (Proxy (..))
import qualified Data.Set                 as Set (fromList,empty) 
import           GHC.Generics
import           Type.Reflection

import           Language.Nominal.Name
import           Language.Nominal.NameSet
import           Language.Nominal.Unify

-- For doctest:

-- $setup
-- >>> :m +Language.Nominal.Nom
-- >>> let [a, b, c] = genUnNom $ freshAtoms [(), (), ()]


{- $intro

A structure is __equivariant__ when it has a trivial swapping action:

> swp _ _ a == a

/__Example:__ Every element of a @Nameless@ type is equivariant./

/__Example:__ The mapping @const True :: Atoms -> Bool@ is equivariant./  

This second example is a particularly important example because it illustrates that "being equivariant" is /not/ the same as "being nameless".  To be equivariant, you only need to be /symmetric/.  

A structure is __equivariant orbit-finite__ when it can be represented by 

* taking finitely many representatives and 
* closing under the swapping action.  
   
/__Example:__ the graph of the identity mapping @id :: Atom -> Atom@ can be represented by closing @[(a,a)]@ under all swappings.  So @id@ is equivariant orbit-finite./
   
Two equivariant orbit-finite maps may be compared for equality even though they may be infinite as functions, because they are finite as representatives-up-to-orbits.
Opearationally for us here in Haskell, it suffices to inspect the representatives and compare them for unifiability using the functions from "Unify". 

We will build:

* An equivariant function type 'KEvFun'.
* An equivariant orbit-finite space of maps 'KEvFinMap', and 
* an equivariant application operation @$$@, for applying a 'KEvFinMap' (which under the hood is just a finite list of representatives) equivariantly to an argument. 

 __Warning:__ When applying a map equivariantly using '$$', It should hold that if @(m $$ a) == b@ then @supp b `isSubsetOf` supp a@.  If not, then unexpected behaviour may result.  The general mathematical reasons for this are discussed with examples e.g. in <http://dx.doi.org/10.4204/EPTCS.34.5 closed nominal rewriting> (see also <http://www.gabbay.org.uk/papers.html#clonre author's pdfs>).  Thus in the terminology of that paper, we need @m@ to be closed.  One way to guarantee this is to ensure that @b@ be @'Nameless'@, so that @b@ is a type like 'Bool' or 'Int' and @supp b@ is guaranteed empty.  In practice for the cases we care about, @b@ will indeed always be @'Nameless'@. 
-}


-- | @'KEvFun' k a b@ is just @a -> b@ in a wrapper.  
-- But, we give this wrapped function trivial swapping and support.  (For a usage example see the source code for 'Language.Nominal.Examples.IdealisedEUTxO.Val'.) 
--
-- Functions need not be finite and are not equality types in general, so we cannot computably test that the actual function wrapped by the programmer actually /does/ have a trivial swapping action (i.e. really is equivariant).  
--
-- It's the programmer's job to only insert truly equivariant functions here.  Non-equivariant elements may lead to incorrect runtime behaviour.  
--
-- On an equivariant orbit-finite type, the compiler can step in with more stringent guarantees.  See e.g. 'KEvFinMap'. 
newtype KEvFun k a b = EvFun { runEvFun :: a -> b -- ^ Function in a wrapper 
                             }

instance KSwappable k (KEvFun k a b) where
   kswp _ _ a = a
instance (Typeable s, KSwappable k a, KSwappable k b) => KSupport (s :: k) (KEvFun k a b) where
   ksupp _ _ = Set.empty
                              
-- | @'Tom'@-equivariant function-space
type EvFun = KEvFun Tom


-- * Equivariant lists and maps

{- $basiclists

Now for some basic functions that filter an input list down to a nub of representatives.  

-}

-- | Filter a list down to one representative from each atoms-orbit (choosing first representative of each orbit). 
kevRep :: KUnifyPerm s a => proxy s -> [a] -> [a]
kevRep = L.nubBy . kunifiablePerm

-- | Instance for @'Tom'@ atom type.
evRep :: UnifyPerm a => [a] -> [a]
evRep = kevRep atTom

-- | Restrict a Map to its equivariant nub, discarding all but one of each key-orbit
kevNub :: (Ord a, KUnifyPerm s a) => proxy s -> DM.Map a b -> DM.Map a b
kevNub p m = DM.restrictKeys m ((Set.fromList . kevRep p . DM.keys) m) 

-- | Instance for unit atom type.
evNub :: (Ord a, UnifyPerm a) => DM.Map a b -> DM.Map a b
evNub = kevNub atTom

-- * Lookup 

{- $lookup

So we have a finite set of representative pairs.  
How do we unify a putative input with a representative to find a matching output?

-}

-- | Equivariantly apply a list of pairs, which we assume represents a map, to an element.
-- Also returns the source element.
kevLookupList' :: (KUnifyPerm s a, KUnifyPerm s b) => proxy s -> [(a, b)] -> a -> Maybe (a, b)
kevLookupList' _ []           _  = Nothing    -- Empty list?  Stop.
kevLookupList' p ((a, b) : t) a' =            -- Nonempty list? 
   let r = kunifyPerm p a a' in               -- fetch unifier, if exists
   if isJustRen r then Just (a, ren r b)      -- if it does, Just apply unifying renaming 
                  else kevLookupList' p t a'  -- otherwise, continue down list. 

-- | Equivariantly apply a list of pairs (which we assume represents a map), to an element
kevLookupList :: (KUnifyPerm s a, KUnifyPerm s b) => proxy s -> [(a,b)] -> a -> Maybe b
kevLookupList p xs a = snd <$> kevLookupList' p xs a

-- | Equivariantly apply a list of pairs (which we assume represents a map), to an element.  @'Tom'@ version.
evLookupList :: (UnifyPerm a, UnifyPerm b) => [(a,b)] -> a -> Maybe b
evLookupList = kevLookupList atTom

-- | Equivariantly apply a map @m@ to an element @a@.  
-- Also returns a unifier.
kevLookup' :: (KUnifyPerm s a, KUnifyPerm s b) => proxy s -> DM.Map a b -> a -> Maybe (a, b)
kevLookup' p m = kevLookupList' p (DM.toList m)

-- | Equivariantly apply a map @m@ to an element @a@.  
-- 
-- * If @a == ren r a'@ for some @r :: Ren@ and @m a' == b'@, 
--
-- * then @kevLookup m a == ren r b'@. 
--
-- For this to work, we require types @a@ and @b@ to support a @'ren'@ action, meaning they should support notions of unification up to permutation.
kevLookup :: (KUnifyPerm s a, KUnifyPerm s b) => proxy s -> DM.Map a b -> a -> Maybe b
kevLookup p m = fmap snd . kevLookup' p m

-- | @'kevLookup'@ instantiated to a @'Tom'@.
evLookup :: (UnifyPerm a, UnifyPerm b) => DM.Map a b -> a -> Maybe b
evLookup = kevLookup atTom



-- * Orbit-finite equivariant maps
{- $orbitfinite


@'KEvFinMap'@ is a type for /orbit-finite/ equivariant maps (contrast with @'KEvFun'@, a type for equivariant functions which need not be orbit-finite).
Values of @'KEvFinMap'@ must be constructed using 

* @'constEvFinMap'@, 
* @'extEvFinMap'@ and 
* @'evFinMap'@.

 Under the hood, @KEvFinMap s a b@ has just one constructor: 

 > DefAndRep b [(a, b)]  

 @DefAndRep@ stands for /Default and list of Representatives/.
 We represent an orbit-finite equivariant map from @a@ to @b@ as 

 * A default value in @b@, and

 * a list of key-value pairs, to be applied up to permuting @s@-sorted atoms in the keys. 

 @DefAndRep@ does not store the atoms it wants permuted, in its structure.  It's just a pair of an element in @b@ and a list of pairs from @[(a, b)]@.  At the point where we use @'$$'@ to equivariantly apply some @DefAndRep@ structure to some argument in @a@, we specify over which atoms we wish to be equivariant.  
 
 Thus: calling this @KEvFinMap@ is convenient but slighly misleading: the equivariance lies in the @'$$'@-/application/ of a @KEvFinMap@-wrapped collection of representatives, to an argument. 

-}

-- | A type for orbit-finite equivariant maps.
data KEvFinMap (s :: k) a b = DefAndRep (Nameless b) [(a, Nameless b)]  
    deriving (Show, Generic, KSwappable k)

-- | We insist @a@ and @b@ be @k@-swappable so that the mathematical notion of support (which is based on nominal sets) makes sense.  
--
-- Operationally, we don't care: if see something of type @KEvFinMap s a b@, we return @Set.empty@.
instance (Typeable (s :: k), KSwappable k a, KSwappable k b) => KSupport s (KEvFinMap s a b) where 
   ksupp _ _ = Set.empty  

-- | @'KEvFinMap'@ at a @'Tom'@.  Thus, a type for orbit-finite @'Tom'@-equivariant maps.
type EvFinMap a b = KEvFinMap 'Tom a b


-- | Equivariant application of an orbit-finite map.  
-- Given a map (expressed as finitely many representative pairs) and an argument ... 
--
-- * it tries to rename atoms to match the argument to the first element of one of its pairs and 
-- * if it finds a match, it maps to the second element of that pair, suitably renamed. 
($$) :: forall s a b. (KUnifyPerm s a, Eq b) => KEvFinMap s a b -> a -> b
DefAndRep (Nameless b') xs $$ a = maybe b' getNameless $ kevLookupList (Proxy :: Proxy s) xs a 

infixr 0 $$

-- | A constant equivariant map. We assume the codomain is @'Nameless'@.
--
-- >>> (constEvFinMap 42 :: EvFinMap Char Int) $$ 'x'
-- 42
--
-- >>> (constEvFinMap 0 :: EvFinMap Atom Int) $$ a
-- 0 
constEvFinMap :: KUnifyPerm s a => b -> KEvFinMap s a b
constEvFinMap b = DefAndRep (Nameless b) []


-- | Extends a map with a new orbit, by specifying a representative @a@ maps to @b@.
-- We assume codomain @b@ is @'Nameless'@, as discussed above. 
--
-- >>> (extEvFinMap 'x' 7 $ (constEvFinMap 42 :: EvFinMap Char Int)) $$ 'x'
-- 7
--
-- >>> (extEvFinMap 'x' 7 $ (constEvFinMap 42 :: EvFinMap Char Int)) $$ 'y'
-- 42
--
-- >>> let [m, n, o] = genUnNom $ freshNames [(), (), ()] 
-- >>> m == n
-- False
-- >>> unifiablePerm m n
-- True
-- >>> (extEvFinMap m 7 $ (constEvFinMap 42 :: EvFinMap (Name ()) Int)) $$ n
-- 7
-- >>> (extEvFinMap o 8 (extEvFinMap m 7 $ (constEvFinMap 42 :: EvFinMap (Name ()) Int))) $$ n
-- 8
extEvFinMap :: forall s a b. (KUnifyPerm s a, Eq a, Eq b) => a -> b -> KEvFinMap s a b -> KEvFinMap s a b
extEvFinMap a b f@(DefAndRep (Nameless b') xs) = case kevLookupList' (Proxy :: Proxy s) xs a of
    Nothing
-- No mapping but sending a to the default value?  Then noop. 
        | b == b'   -> f  
-- No mapping and not sending a to the default value?  Add (a,b)
        | otherwise -> DefAndRep (Nameless b') $ (a, Nameless b) : xs  
    Just (a'', Nameless b'')
-- (a,b) is already there, up to permuting atoms in a (b is nameless).  Noop.
        | b == b''  -> f
-- (a,b) is not already there up to permuting atoms in a.  Remove (a'',b'') and replace with (a'',b).  We really rely on b being nameless, here.
        | otherwise -> DefAndRep (Nameless b') [(c, if c == a'' then Nameless b else d) | (c, d) <- xs]

-- | Constructs an orbit-finite equivariant map by prescribing a default value, and
-- finitely many argument-value pairs.
-- We assume the codomain is @'Nameless'@, as discussed above. 
--
-- >>> let f = evFinMap 42 [('x', 7), ('y', 5), ('x', 13)] :: EvFinMap Char Int
-- >>> map (f $$) ['x', 'y', 'z']
-- [13,5,42]
--
-- >>> let atmEq = evFinMap False [((a,a), True)] :: EvFinMap (Atom, Atom) Bool 
-- >>> map (atmEq $$) [(b,b), (c,c), (a,c), (b,c)]
-- [True,True,False,False]
--
-- >>> let g = evFinMap 2 [((a,a), 0), ((b,c), 1)] :: EvFinMap (Atom, Atom) Int 
-- >>> map (g $$) [(b,b), (c,c), (a,c), (b,c)]
-- [0,0,1,1]
evFinMap :: (KUnifyPerm s a, Eq a, Eq b) 
         => b             -- ^ Default value.
         -> [(a, b)]      -- ^ List of exceptional argument-value pairs. In case of conflict, later pairs overwrite earlier pairs.
         -> KEvFinMap s a b
evFinMap = L.foldl' (\m (a, b) -> extEvFinMap a b m) . constEvFinMap

-- | Extracts default value und list of exceptional argument-value pairs from an @'EvFinMap'@.
--
-- >>> fromEvFinMap $ (evFinMap 42 [('x', 7), ('y', 5), ('x', 13)] :: EvFinMap Char Int)
-- (42,[('y',5),('x',13)])
--
fromEvFinMap :: KEvFinMap s a b -> (b, [(a, b)])
fromEvFinMap (DefAndRep (Nameless b') xs) = (b', [(a, b) | (a, Nameless b) <- xs])

-- | 'KEvFinMap' is compared for equality by comparing the default value and the representatives, up to permutations.  
--
-- __Edge case:__ If a codomain type is orbit-finite (e.g. @'Bool'@ and @'(Atom,Atom)'@, with two orbits, or @'Atom'@ with one), and representatives exhaust all possibilities, then the default value will never be queried, yet it will still be considered in our equality test.  
instance (KUnifyPerm s a, Eq b) => Eq (KEvFinMap s a b) where
    f1@(DefAndRep b1 xs1) == f2@(DefAndRep b2 xs2)
        =    (b1 == b2)                                    -- default values equal?
          && all (\(a, Nameless b) -> (f2 $$ a) == b) xs1  -- check equality by representatives 
          && all (\(a, Nameless b) -> (f1 $$ a) == b) xs2
-- TODO: replace with extensionality test

-- This looks like 'Nameless', but 'Nameless' cannot be parameterised over s.
instance (KUnifyPerm s a, KUnifyPerm s b, Eq b) => KUnifyPerm s (KEvFinMap s a b) where
    kunifyPerm _ f g   
        | f == g    = mempty
        | otherwise = Ren Nothing
    ren = const id


{- $tests Property-based tests are in "Language.Nominal.Properties.EquivarSpec". -}

