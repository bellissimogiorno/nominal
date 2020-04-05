{-|
Module      : Abs 
Description : Nominal atoms-abstraction types 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

Name-abstraction, nominal style
-}


{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}  -- needed for Num a => Nameless a
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE PartialTypeSignatures #-}  

module Language.Nominal.Abs 
    where

import Language.Nominal.Names 
import Language.Nominal.Nom

-- * Name-abstraction


-- | An abstraction contains a label, and a lambda-abstraction.  
newtype Abs t a = Abs (Maybe t, Name t -> a)

-- We could also set `Abs t a = Abs (Nom t (Name t, a))`, but this would make later type signatures more complex, e.g. by requiring `Swappable t a` in 'conc' and '@@'.

-- | Create an abstraction by providing a name and a datum in which that name can be swapped (straight out of the paper; <https://link.springer.com/article/10.1007/s001650200016 publisher> and <http://www.gabbay.org.uk/papers.html#newaas-jv author's> pdfs).
absByName :: Swappable t a => Name t -> a -> Abs t a
absByName nam a = 
   let t = nameLabel nam in 
      Abs (t, \nam' -> swp (nameOverwriteLabel t nam') nam a) -- nameOverwriteLabel may not be required 

-- | Concrete an abstraction at a name.  Unsafe if the name is not fresh for @a@.
conc :: Abs t a -> Name t -> a
conc (Abs (t', f)) nam = f $ nameOverwriteLabel t' nam -- perhaps should check if t is nothing, and if so take label from nam instead?


-- | Concretion.  To destroy an abstraction x', provide it with an f and calculate x' @@ f.
-- This unpacks x' as (n,x) for a fresh name n, and calculates f n x.
(@@) :: Abs t a -> (Name t -> a -> b) -> b
(@@) x f = unsafeUnNom $ x @> f
{-- (@@) (Abs (t', f')) f = unsafeUnNom $ do -- Nom monad
   nam <- freshNameNom t'
   return $ f nam (f' nam) 
--}

infixr 9 @@

-- | Version of concretion '@@' that leaves the fresh name in a 'Nom' binding. 
(@>) :: Abs t a -> (Name t -> a -> b) -> Nom t b
(@>) (Abs (t', f')) f = do -- Nom monad
   nam <- freshNameNom t'
   return $ f nam (f' nam) 

infixr 9 @>

-- | Bijection between @Nom@ and @Abs@
absToNom :: Abs t a -> Nom t (Name t,a)
absToNom a' = a' @> \n a -> (n, a)

-- | Bijection between @Nom@ and @Abs@.
nomToAbs :: Swappable t a => Nom t (Name t,a) -> Abs t a
nomToAbs a' = unsafeUnNom $ -- unsafeUnNom is guaranteed safe here because we know @n@ is abstracted. 
   do -- Nom monad
      (n, a)  <- a'
      return $ absByName n a

-- | Fuse two abstractions, taking label of abstracted name from first argument.
fuse :: (Abs t a1, Abs t a2) -> Abs t (a1, a2)
fuse (Abs (t1, f1), Abs (_, f2)) = 
   Abs (t1, \n -> let n' = nameOverwriteLabel t1 n in (f1 n', f2 n'))

-- | Split two abstractions
unfuse :: Abs t (a1, a2) -> (Abs t a1, Abs t a2) 
unfuse (Abs (t, f)) = 
   (Abs (t, fst . f), Abs (t, snd . f))



-- * Unpacking name-contexts and abstractions


-- | Abstractions are equal up to fusing their abstracted names. 
instance (Eq t, Eq a) => Eq (Abs t a) where
   Abs (t1, f1) == Abs(t2, f2) = 
      (t1 == t2) && 
      unsafeUnNom (do -- Nom monad
         nam <- freshNameNom t1
         return $ f1 nam == f2 nam
         )

-- mjg swp overlap here
-- mjg explain
instance (Swappable n a, Swappable n t, Swappable n (Name t)) => Swappable n (Abs t a) where 
   swp n1 n2 (Abs x) = Abs $ swp n1 n2 x 
--   swp n1 n2 (Abs (t, f)) = Abs (swp n1 n2 t, \x -> swp n1 n2 (f (swp n1 n2 x))) 


-- | We show an abstraction by evaluating the function inside `Abs` on a fresh name (with the default `Nothing` label)
instance (Show t, Show a) => Show (Abs t a) where
   show a' = a' @@ \n a -> show n ++ ". " ++ show a

instance Functor (Abs t) where
   fmap :: (a -> b) -> Abs t a -> Abs t b
   fmap g (Abs (t, f)) = Abs (t, g . f)

instance Applicative (Abs t) where
   pure  :: a -> Abs t a
   pure a = Abs (Nothing, const a)
   (<*>) :: Abs t (a -> b) -> Abs t a -> Abs t b
   (<*>) (Abs (tg, g)) (Abs (_, a)) = Abs (tg, \nam -> let nam' = nameOverwriteLabel tg nam in g nam' $ a nam') -- must choose one of the two labels


-- | Apply f to a fresh element with label @Just t@
absFresh :: Swappable t a => t -> (Name t -> a) -> Abs t a
-- absFresh f = Abs f
absFresh t f = unsafeUnNom . atFresh t $ \m -> absByName m (f m)

-- | Apply f to a fresh element with label `Nothing` 
absFresh' :: Swappable t a => (Name t -> a) -> Abs t a
absFresh' f = unsafeUnNom . atFresh' $ \m -> absByName m (f m)


-- [mjg improve exposition]
-- | near inverse to applicative distribution; absFuncIn . absFuncOut = id but not necessarily other way around 
absFuncOut :: Swappable n a => (Abs n a -> Abs n b) -> Abs n (a -> b)
absFuncOut f = Abs (Nothing, \nam a -> conc (f (absByName nam a)) nam)

