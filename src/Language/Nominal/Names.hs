{-|
Module      : Names 
Description : Nominal theory of names and swappings
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Nominal theory of names and swappings
-}

{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}  -- needed for Num a => Nameless a
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE PartialTypeSignatures #-}  

module Language.Nominal.Names 
{-    ( Name
    , nameLabel
    , freshNameIO
    , freshNamesIO
    , nameOverwriteLabel
    , Perm
    , perm
    , Swappable
    , swp
    , swp' 
    ) -}
    where

import           Data.Unique
import qualified Data.Map as DM 


import Language.Nominal.Utilities


-- * Names and atoms

-- | An atom is a unique atomic token
newtype Atom = Atom Unique
   deriving (Eq, Ord)

-- | Display atoms 
instance Show Atom where
   show (Atom a) = "_" ++ show (hashUnique a)
{--   show a = fromMaybe ("_" ++ (show (hashUnique a))) (do -- Maybe monad
      i <- elemIndex a myatoms
      return $ myatomnames !! i) 
--}

-- | A name is a pair of an atom and its label 't'.  
-- Think of 't' loosely as the name's type.  
-- We use 'Maybe' so there is a default label if we want to create a fresh atom.
newtype Name t = Name (Maybe t, Atom)
   deriving (Ord)

-- | Fetch label of name
nameLabel :: Name t -> Maybe t
nameLabel (Name(t', _)) = t'

-- | Fetch atom of name
nameAtom :: Name t -> Atom 
nameAtom (Name(_, atm)) = atm 

-- | Names are equal when they refer to the same atom.
-- Labels are not considered. 
instance Eq (Name t) where
   Name (_, atm1) == Name (_, atm2) = atm1 == atm2 

instance Show t => Show (Name t) where
   show nam = show (nameLabel nam) ++ show (nameAtom nam)
instance {-# OVERLAPPING #-} Show (Name ()) where
   show nam = "n" ++ show (nameAtom nam)

-- | Create a fresh name with the specified label, inside the IO monad.
freshNameIO :: Maybe t -> IO (Name t)
freshNameIO t' = do -- IO monad
   u <- newUnique
   return $ Name(t', Atom u) 

-- | Freshen a list of names.  Labels carried over; atoms freshened.
freshNamesIO :: [Name t] -> IO [Name t]
freshNamesIO = mapM (freshNameIO . nameLabel) 

-- | Functorial action on names.  Acts on the name's label.
instance Functor Name where
  fmap :: (s -> t) -> Name s -> Name t
  fmap f (Name (s', atm)) = Name (f <$> s', atm)  

{-- mjg to restore? instance Applicative Name where
  pure :: t -> Name t
  (<*>) :: Name (s -> t) -> Name s -> Name t
  pure s = unsafePerformIO . freshName $ Just s
  (<*>) = ap --}

-- | As the name suggests: overwrite the name's label
nameOverwriteLabel :: Maybe t -> Name t -> Name t
nameOverwriteLabel t' (Name (_, atm)) = Name (t', atm)

-- | A permutation represented as a list of swappings.
type Perm a = [(a,a)] 

-- | Types that admit a swapping action.  A swapping (a b) maps a to b and b to a and leaves all other names unchanged.  Swappings are invertible, which allows them to commute through type-formers containing negative arities, e.g. the left-hand argument of function arrow.  A permutation is just a chain of swappings.
class Swappable t a where
   swp :: Name t -> Name t -> a -> a          --  swap n and n' in a
   perm :: Perm (Name t) -> a -> a          --  chain swappings 
   perm = chain . map (uncurry swp)  

instance (Swappable t a, Swappable t b) => Swappable t (a,b) where
   swp n1 n2 (a,b) = (swp n1 n2 a, swp n1 n2 b) 
instance (Swappable t a, Swappable t b, Swappable t c) => Swappable t (a,b,c) where
   swp n1 n2 (a,b,c) = (swp n1 n2 a, swp n1 n2 b, swp n1 n2 c) 
instance (Swappable t a, Swappable t b, Swappable t c, Swappable t d) => Swappable t (a,b,c,d) where
   swp n1 n2 (a,b,c,d) = (swp n1 n2 a, swp n1 n2 b, swp n1 n2 c, swp n1 n2 d) 

instance Swappable t a => Swappable t [a] where
   swp n1 n2 = map (swp n1 n2)

-- | swappability distributes over function types, because functions inherit swapping action pointwise
instance (Swappable t a, Swappable t b) => Swappable t (a -> b) where
   swp n1 n2 f = swp n1 n2 . f . swp n1 n2 

-- | swappability distributes over map types, because functions inherit swapping action pointwise
instance (Swappable t a, Swappable t b, Ord a) => Swappable t (DM.Map a b) where
   swp n1 n2 m = DM.fromList $ swp n1 n2 (DM.toList m)  -- mjg this is probably a bit brutal

instance Swappable n t => Swappable n (Maybe t) where
   swp  _  _ Nothing  = Nothing
   swp n1 n2 (Just t) = Just $ swp n1 n2 t 


-- mjg overlapping instances
-- swap should preserve labels
-- discuss & explain
-- swp' maps n1 to n2-with-n1's-label and vice-versa

-- | Base case for swapping: t-labelled names acting on themselves.
-- Only atoms are swapped; labels aren't touched; counterintuitive if label is display name, but arguably stands a better chance of being the right thing if label is a type or carries other semantic information.
swp' :: Name t -> Name t -> Name t -> Name t
swp' n1 n2 n 
   | n == n1   = nameOverwriteLabel (nameLabel n1) n2 
   | n == n2   = nameOverwriteLabel (nameLabel n2) n1 
   | otherwise = n


-- Need {-# LANGUAGE OverlappingInstances #-} for these two
instance Swappable t (Name t) where
   swp = swp' 
-- mjg swp overlap here
{-- instance Swappable n t => Swappable n (Name t) where
   swp n1 n2 (Name (t', atm)) = Name (swp n1 n2 t', atm) -}




