{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Read where

import Prelude hiding (Read)
import Hefty
import Hefty.Compilation.Common

data Read c m a where
  Read :: Read c m (c Val)

instance HFunctor (Read c) where
  hmap _ Read = Read

read :: Read c << h => Hefty h (c Val)
read = send Read