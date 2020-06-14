{-|
Module      : Algebraic graphs with binding 
Description : Extending algebraic graphs with nominal-style binding 
Copyright   : (c) Murdoch J. Gabbay, 2020
License     : GPL-3
Maintainer  : murdoch.gabbay@gmail.com
Stability   : experimental
Portability : POSIX

This file is under development.

-}

{-# LANGUAGE InstanceSigs          
           , DeriveGeneric         
           , FlexibleContexts 
           , LambdaCase 
           , MultiParamTypeClasses 
           , DeriveAnyClass       -- to derive 'Swappable' 
           , DeriveDataTypeable   -- to derive 'Data' 
           , FlexibleInstances     
           , TypeOperators        -- to use :. in instances
#-}


module Language.Nominal.Examples.Graph
    where

import GHC.Generics
-- import Data.Generics     hiding (Generic, typeOf)
-- import Algebra.Graph.HigherKinded.Class 
-- import Control.Compose -- for :.
-- import Data.Function    ((&))

import Language.Nominal.Name 
import Language.Nominal.NameSet 
import Language.Nominal.Nom

-- | Should parameterise over atom type (see 'KAtom').  For now, I use the default atom type 'Tom'.
data Graph a = Empty
             | Vertex a
             | Overlay (Graph a) (Graph a)
             | Connect (Graph a) (Graph a)
             | Restrict (Nom (Graph a))
             deriving (Show, Generic, Swappable)

-- | Restriction action just passes the restriction on to the deep embedding
instance Swappable a => KRestrict Tom (Graph a) where
   restrict atms g = Restrict (res atms g)

-- | Fold on graphs with binding.  
-- Just like fold on graphs, but with an extra restriction operation, which we go under in a capture-avoiding manner. 
foldg :: b -> (a -> b) -> (b -> b -> b) -> (b -> b -> b) -> (Nom b -> b) -> Graph a -> b
foldg e v o c r = go
  where
    go Empty         = e
    go (Vertex  x  ) = v x
    go (Overlay x y) = o (go x) (go y)
    go (Connect x y) = c (go x) (go y)
    go (Restrict x') = r (go <$> x') -- special operators, like @@! and @@., are available to construct @r@. 
{-# INLINE [0] foldg #-}

-- | Filter a list of vertices to obtain those vertices for which @atms :: ['Atom']@ is fresh 
filterApart :: Support a => [Atom] -> [a] -> [a]
filterApart atms = filter $ apart atms

{- instance Graph g => Graph ((KNom s) :. g) where
   connect :: (KNom s :. g) a -> (KNom s :. g) a -> (KNom s :. g) a
   connect g1' g2' = O $ (unO g1') @@. \gas1 g1 -> (unO g2') @@. \gas2 g2 ->
      let h1 = filter (kapart (Proxy :: Proxy s) gas1) (vertices g1) 
          h2 = filter (kapart (Proxy :: Proxy s) gas2) (vertices g2) 
      in
          res $ g1 <|> g2 <|> (biclique h1 h2)
-}
   
{-
   connect g1' g2' = O $ (genUnNom' . unO $ g1') & \(gas1, g1) -> (genUnNom' . unO $ g2') & \(gas2, g2) ->
      let h1 = filter (kapart gas1) (vertices g1) 
          h2 = filter (kapart gas2) (vertices g2) 
      in
          res $ g1 <|> g2 <|> (biclique h1 h2)
-}
