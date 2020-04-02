module Language.Nominal.Properties.AbsSpec
     where

import Test.QuickCheck

import Language.Nominal.Names 
import Language.Nominal.Nom
import Language.Nominal.Abs

-- | @fuse a.x a.x' = a.(x,x')@
prop_fuse :: Name () -> [Name ()] -> [Name ()] -> Bool
prop_fuse n a b = fuse (absByName n a, absByName n b) == absByName n (a,b)

-- | @n # x => [n](x @ n) = x@
prop_Abs_Conc :: Name () -> Abs () [Name ()] -> Property 
prop_Abs_Conc n x = isFresh n x ==> (absByName n (conc x n) === x) 

-- | @n' # x => [n]x = [n'](n' n).x@
prop_Abs_alpha :: Name () -> Name () -> [Name()] -> Property
prop_Abs_alpha n n' l = (isFresh n' l) ==> (absByName n l === absByName n' (swp n' n l))

-- | @(n.x) \@ n = x@
prop_Conc_Abs :: Name () -> [Name ()] -> Property 
prop_Conc_Abs n x = conc (absByName n x) n === x

-- | @(n.x) \@ n = x@
prop_Conc_Abs_swap :: Name () -> Name () -> [Name ()] -> Property 
prop_Conc_Abs_swap n n' x = isFresh n' x ==> conc (absByName n x) n' === swp n' n x

{-- pprop_Abs_Fresh :: [Name ()] -> Name () -> Property 
prop_Abs_Fresh x n = isFresh n x ==> conc (unsafeUnNom $ atFresh' (\n' -> absByName n' x)) n === x --}

-- | Atm.(X x Y) iso Atm.X x Atm.Y, left-to-right-to-left
prop_fuse_unfuse_Abs :: Abs () ([Name ()], [Name ()]) -> Property 
prop_fuse_unfuse_Abs a = (fuse . unfuse) a === a

-- | Atm.(X x Y) iso Atm.X x Atm.Y, right-to-left-to-right
prop_unfuse_fuse_Abs :: (Abs () [Name ()], Abs () [Name ()]) -> Property 
prop_unfuse_fuse_Abs (a1, a2) = (unfuse . fuse) (a1, a2) === (a1, a2)

-- | Iso fails if atoms labelled, since one label lost Atm.X x Atm.Y -> Atm.(X x Y) 
prop_unfuse_fuse_Abs' :: (Abs Int [Name Int], Abs Int [Name Int]) -> Property 
prop_unfuse_fuse_Abs' (a1, a2) = expectFailure ( (unfuse . fuse) (a1, a2) === (a1, a2) )

-- | Atm.X iso Nom (Atm x X)
prop_abs_to_nom :: Abs Int [Name Int] -> Bool
prop_abs_to_nom x' = x' == (nomToAbs (absToNom x'))

{-- | expect failure here only because of local scopes
prop_nom_to_abs' :: Nom Int (Name Int, [Name Int]) -> Property 
prop_nom_to_abs' x' = expectFailure $ x' == (absToNom (nomToAbs x'))
--}

{-- mjg arbitrary needed here
prop_nom_to_abs :: Nom Int (Name Int, [Name Int]) -> Bool 
prop_nom_to_abs x' = unNom $ do -- Nom monad
   (m, x) <- x' 
   (n, y) <- absToNom (nomToAbs x') 
   return $ swp m n y == x
-}

