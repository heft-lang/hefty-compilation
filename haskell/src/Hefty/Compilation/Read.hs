{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Read where

import Prelude hiding (Read)
import Hefty

data Read c m a where
  Read :: Read c m (c Int)

instance HFunctor (Read c) where
  hmap _ Read = Read

read :: Read c << h => Hefty h (c Int)
read = send Read