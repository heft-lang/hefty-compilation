{-# LANGUAGE GADTs #-}
module Hefty.Compilation.Read where

import Prelude hiding (Read)
import Hefty
import Hefty.Compilation.Common

data Read c m a where
  Read :: Read c m (c Val)

instance HTraversable (Read c) where
  htraverse _ Read = pure Read

instance Alpha (Read c m a) where
  rename _ _ Read = Read

read :: (Fresh < t, Read Name << h) => TL t h (Name Val)
read = sendR Read