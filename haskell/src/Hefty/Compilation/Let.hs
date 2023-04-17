{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
module Hefty.Compilation.Let where

import Hefty
import Hefty.Compilation.Common

data Let m a where
  Let :: m (Name Val) -> Name Val -> m (Name Val) -> Let m (Name Val)

instance HTraversable Let where
  htraverse f (Let m n b) = (`Let` n) <$> f m <*> f b

instance Alpha (m (Name Val)) => Alpha (Let m a) where
  rename v v' (Let x n y) = Let (rename v v' x) (rename v v' n) (rename v v' y)

let' :: (Fresh < t, Let << h) => TL t h (Name Val) -> (Name Val -> TL t h (Name Val)) -> TL t h (Name Val)
let' m f = do I n <- sendC Fresh; m' <- flush m; f' <- flush (f n); sendR (Let m' n f')