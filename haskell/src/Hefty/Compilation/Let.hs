{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Let where

import Hefty

data Let c m a where
  Let :: m (c Int) -> (c Int -> m (c Int)) -> Let c m (c Int)

instance HFunctor (Let c) where
  hmap f (Let m b) = Let (f m) (f . b)

let' :: (Let c << h) => Hefty h (c Int) -> (c Int -> Hefty h (c Int)) -> Hefty h (c Int)
let' m f = Op (injH $ Let m f) Return