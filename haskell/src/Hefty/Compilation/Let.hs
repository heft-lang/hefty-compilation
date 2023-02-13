{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Let where

import Hefty

data Let c m a where
  Let :: m (c a) -> (c a -> m (c b)) -> Let c m (c b)

instance HFunctor (Let c) where
  hmap f (Let m b) = Let (f m) (f . b)

let' :: (Let c << h) => Hefty h (c a) -> (c a -> Hefty h (c b)) -> Hefty h (c b)
let' m f = Op (injH $ Let m f) Return