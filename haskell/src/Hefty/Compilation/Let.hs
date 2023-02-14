{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Let where

import Hefty
import Hefty.Compilation.Common

data Let c m a where
  Let :: m (c Val) -> (c Val -> m (c Val)) -> Let c m (c Val)

instance HFunctor (Let c) where
  hmap f (Let m b) = Let (f m) (f . b)

let' :: (Let c << h) => Hefty h (c Val) -> (c Val -> Hefty h (c Val)) -> Hefty h (c Val)
let' m f = Op (injH $ Let m f) Return