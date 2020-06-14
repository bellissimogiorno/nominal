{-# LANGUAGE FlexibleContexts      #-}  -- for non-type variable argument in constraint, namely Support and Swappable
{-# LANGUAGE DataKinds             #-}  -- for Tom
{-# LANGUAGE ScopedTypeVariables   #-}

module Language.Nominal.Properties.NomSpec
    where

import Data.Function   (on, (&))
import Data.Set        as S
import Data.Default
import Data.List.Extra as LE
import Test.QuickCheck

import Language.Nominal.Name
import Language.Nominal.NameSet
import Language.Nominal.Nom
import Language.Nominal.Binder
-- import Language.Nominal.Unify
import Language.Nominal.Properties.SpecUtilities ()

-- | Nom creates local binding, which is unpacked separately by equality.  Cf. `UnifySpec` to see how this can be addressed.
prop_x_neq_x :: Nom [Name Int] -> Property
prop_x_neq_x x = expectFailure $ x == x

-- | Check restriction creates local scope.
-- Should return False.
prop_split_scope :: Name String -> Bool
prop_split_scope n = unNom $ do -- Nom monad
   let (x1,x2) = (resN [n] n, resN [n] n) -- create two scopes
   y1 <- x1                             -- unpack them
   y2 <- x2
   return $ y1 /= y2                    -- check for equality

-- | n' # n if n' is chosen fresh, after n
prop_fresh_neq :: Name () -> Bool
prop_fresh_neq n = unNom $ do -- Nom monad
   n' <- freshName ()
   return $ n /= n'

-- | @freshName () /= freshName ()@  Lazy evaluation means distinct fresh names generated.
prop_fresh_neq' :: Bool
prop_fresh_neq' = let x = freshName () in x /= x

-- | Same thing using @let@.
prop_fresh_neq'' :: Bool
prop_fresh_neq'' = let x = exit (freshName ()) in x == x

-- | But if we unpack a single fresh name monadically, we can compare it for equality.
prop_fresh_eq :: Bool
prop_fresh_eq =
   let x' = freshName () in
   unNom $ do -- Nom monad
      x <- x'
      return $ x == x


-- | @~ (n # (n,n'))@
prop_freshFor1 :: Name () -> Name () -> Bool
prop_freshFor1 n n' = not $ n `freshFor` (n,n')

-- | @n # n'@
prop_freshFor2 :: Name () -> Bool
prop_freshFor2 n = unNom $ do -- Nom monad
   n' <- freshName ()
   return $ n `freshFor` n'

-- | Nom Maybe -> Maybe Nom -> Nom Maybe = id
prop_transposeNomMaybe :: Nom (Maybe [Name Int]) -> Bool
prop_transposeNomMaybe x' = unNom $ do -- Nom monad
    l1' <- x'  -- Maybe get a list of names
    l2' <- transposeFM (transposeMF x') -- Maybe get another list of names (freshening means the atoms will be different)
    -- l2' <- transposeTraversableNom (transposeNomFunc x') -- Maybe get another list of names (freshening means the atoms will be different)
    return $ ((==) `on` fmap (fmap nameLabel)) l1' l2' -- first fmap for Maybe, second for list

-- | Maybe Nom -> Nom Maybe -> Nom Maybe = id
prop_transposeMaybeNom :: Maybe (Nom [Name Int]) -> Bool
prop_transposeMaybeNom x' =
    let y' = transposeMF (transposeFM x')
    -- let y' = transposeNomFunc (transposeTraversableNom x')
    in  case (x', y') of
            (Nothing,  Nothing)  -> True
            (Just l1', Just l2') -> unNom $ ((==) `on` fmap nameLabel) <$> l1' <*> l2' -- fmap is for list, <$> <*> is for Nom
            _                    -> False


-- a,b#x |- (a b).x = x
prop_new' :: [Name Int] -> Bool
prop_new' l = (new :: Int -> (Name Int -> Bool) -> Bool) def $ \a -> new def $ \b -> (swpN a b l) == l

-- a#x |/- (a b).x = x (cf. 'Language.Nominal.Properties.NameSpec.prop_singleswap')
prop_not_new' :: [Name Int] -> Name Int -> Property
prop_not_new' l b = expectFailure $ new def $ \a -> (swpN a b l) == l

-- a,b#x |- (a b).x = x
prop_new :: Int -> Int -> [Name Int] -> Bool
prop_new ta tb l = (new :: Int -> (Name Int -> Bool) -> Bool) ta $ \a -> new tb $ \b -> (swpN a b l) == l

-- n#l iff n not in l, for n a name and l a list of names
prop_freshFor_notElem :: Name () -> [Name ()] -> Bool
prop_freshFor_notElem n ns = not (n `elem` ns) == (n `freshFor` ns)

-- atoms-restriction precisely removes atoms from support
iprop_support_nom :: forall a. (Support a, Swappable a) => [Atom] -> a -> Bool
iprop_support_nom atms a = supp ((atms @> a) :: Nom a) == (supp a) S.\\ (S.fromList atms)

prop_support_nom_atmlist :: [Atom] -> [Atom] -> Bool
prop_support_nom_atmlist = iprop_support_nom

prop_support_nom_nomatmlist :: [Atom] -> Nom [Atom] -> Bool
prop_support_nom_nomatmlist = iprop_support_nom

-- if we freshen all atoms in an element, its support is apart from the original
iprop_freshen_apart :: (Support a, Swappable a) => a -> Bool
iprop_freshen_apart a = unNom $ (kfreshen atTom a) >>= \a' -> return $ a' `apart` a

prop_freshen_apart_atmlist :: [Atom] -> Bool
prop_freshen_apart_atmlist = iprop_freshen_apart

prop_freshen_apart_nom_atmlist :: Nom [Atom] -> Bool
prop_freshen_apart_nom_atmlist = iprop_freshen_apart

-- a freshened list of atoms is disjoint from its original
prop_freshen_apart_disjoint :: [Atom] -> Bool
prop_freshen_apart_disjoint as = unNom $ (freshen as) >>= \as' -> return $ as' `LE.disjoint` as

-- two notions of trivial Nom binding are equal, on a type with both Support and Swappable+Eq
prop_isTrivial_equal :: Nom [Atom] -> Bool
prop_isTrivial_equal x = isTrivialNomBySupp x == isTrivialNomByEq x

-- isTrivial sanity check (supp version)
prop_isTrivial_sane :: Nom [Atom] -> Property
prop_isTrivial_sane x = expectFailure $ isTrivialNomBySupp x

-- isTrivial sanity check (freshFor version)
prop_isTrivial_sane' :: Nom [Atom] -> Property
prop_isTrivial_sane' x = expectFailure $ isTrivialNomByEq x


deBruijnAcc :: KNom s a -> (KAtom s -> b) -> b -> (a, KAtom s -> b)
deBruijnAcc a' f b = exitWith (\atms a -> (a, \atm -> if (atm `elem` atms) then b else f atm)) a'  
-- deBruijnAcc a' f b = (exitWith (,) a') & \(atms, a) -> (a, \atm -> if (atm `elem` atms) then b else f atm)

deBruijn1 :: Functor f => KNom s (f (KAtom s)) -> f Int
deBruijn1 a' = (deBruijnAcc a' (\_ -> 0) 1) & \(a, f) -> f <$> a

deBruijn2 :: Functor f => KNom s (KNom s (f (KAtom s)))-> f Int
deBruijn2 a'' = (deBruijnAcc a'' (\_ -> 0) 1) & \(a', f') -> (deBruijnAcc a' f' 2) & \(a, f) -> f <$> a

-- | Commute Nom and List
prop_transposeNomList :: Nom [Atom] -> Property
prop_transposeNomList x' = deBruijn1 x' === deBruijn1 (transposeFM (transposeMF x'))
-- prop_transposeNomList x' = deBruijn1 x' === deBruijn1 (transposeTraversableNom (transposeNomFunc x'))

-- | Commute Nom and Nom (one way)
prop_transposeNomNom :: Nom (Nom [Atom]) -> Property
prop_transposeNomNom x'' = deBruijn2 x'' === deBruijn2 (transposeMF $ transposeMF x'')
-- prop_transposeNomNom x'' = deBruijn2 x'' === deBruijn2 (transposeNomFunc $ transposeNomFunc x'')

{-- | Commute List and Nom
prop_transposeListNom :: [Nom Atom] -> Bool
prop_transposeListNom x' = (deBruijn1 <$> x') == (deBruijn1 (transposeNomFunc (transposeTraversableNom x')))
--}
