{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
module Hefty.Compilation.Cond where
import Hefty
import Hefty.Compilation.Common
import Data.Bool (bool)


data Cond c m a where
  -- See note [Scoped If]
  CIf :: c Val -> m (c Val) -> m (c Val) -> Cond c m (c Val)
  CFalse, CTrue :: Cond c m (c Val)
  Cmp :: CC -> c Val -> c Val -> Cond c m (c Val)
  Not :: c Val -> Cond c m (c Val)

-- Note [Scoped If]
-- You could also imagine an unscoped if:
--     CIf :: c Val -> Cond c m Bool
-- However, then you'd duplicate the whole remainder of the program
-- over both branches.

instance HFunctor (Cond c) where
  hmap h (CIf c t f) = CIf c (h t) (h f)
  hmap _ CFalse = CFalse
  hmap _ CTrue = CTrue
  hmap _ (Cmp cc x y) = Cmp cc x y
  hmap _ (Not x) = Not x

if' :: (HFunctor h, Cond c << h) => c Val -> Hefty h (c Val) -> Hefty h (c Val) -> Hefty h (c Val)
if' c t f = send (CIf c t f)

false, true :: Cond c << h => Hefty h (c Val)
false = send CFalse
true = send CTrue

cmp :: Cond c << h => CC -> c Val -> c Val -> Hefty h (c Val)
cmp cc x y = send (Cmp cc x y)

not :: Cond c << h => c Val -> Hefty h (c Val)
not x = send (Not x)