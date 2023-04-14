{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Let where

import Hefty
import Hefty.Compilation.Common

data Let m a where
  Let :: m (Name Val) -> Name Val -> m (Name Val) -> Let m (Name Val)

instance HTraversable Let where
  htraverse f (Let m n b) = (`Let` n) <$> f m <*> f b

let' :: (Fresh < t, Let << h) => TL t h (Name Val) -> (Name Val -> TL t h (Name Val)) -> TL t h (Name Val)
let' m f = do I n <- sendC Fresh; m' <- flush m; f' <- flush (f n); sendR (Let m' n f')