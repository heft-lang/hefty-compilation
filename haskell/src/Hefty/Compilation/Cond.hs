{-# LANGUAGE GADTs #-}

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
-- However, then you'd duplicate the whole remainder of the program over both branches.

instance HTraversable (Cond Name) where
  htraverse h (CIf c t f) = CIf c <$> h t <*> h f
  htraverse _ CFalse = pure CFalse
  htraverse _ CTrue = pure CTrue
  htraverse _ (Cmp cc x y) = pure $ Cmp cc x y
  htraverse _ (Not x) = pure $ Not x

if' :: (HTraversable h, Fresh < t, Cond Name << h) => Name Val -> TL t h (Name Val) -> TL t h (Name Val) -> TL t h (Name Val)
if' c t f = flush t >>= \t' -> flush f >>= \f' -> sendR (CIf c t' f')

false, true :: (Fresh < t, Cond Name << h) => TL t h (Name Val)
false = sendR CFalse
true = sendR CTrue

cmp :: (Fresh < t, Cond Name << h) => CC -> Name Val -> Name Val -> TL t h (Name Val)
cmp cc x y = sendR (Cmp cc x y)

not :: (Fresh < t, Cond Name << h) => Name Val -> TL t h (Name Val)
not x = sendR (Not x)