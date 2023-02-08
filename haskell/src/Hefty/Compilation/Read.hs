module Hefty.Compilation.Read where

import Prelude hiding (Read)
import Hefty.Algebraic

data Read c a where
  Read :: Read c (c Int)

read :: In eff (Read c) f => eff f (c Int)
read = lift Read