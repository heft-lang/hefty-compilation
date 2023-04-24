{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Hefty.Compilation.Block where

import Hefty.Compilation.Common
import Hefty
import Data.Void

data Block m a where
  Blocks :: [(Label, m (Name ()))] -> Block m (Name ()) 
  Jmp :: Label -> Block m a

deriving instance (Show (m (Name ()))) => Show (Block m a)

instance HTraversable Block where
  htraverse f (Blocks xs) = Blocks <$> traverse (\(x,y) -> (x,) <$> f y) xs
  htraverse _ (Jmp lbl) = pure $ Jmp lbl

instance (forall x. Alpha (m (Name x))) => Alpha (Block m a) where
  rename v v' (Blocks bs) = Blocks (rename v v' bs)
  rename _ _ (Jmp l) = Jmp l


blocks :: (Fresh < t, Block << h) => [(Label, TL t h (Name ()))] -> TL t h (Name ())
blocks blks = traverse (traverse flush) blks >>= \blks' -> sendR (Blocks blks')

jmp :: (Fresh < t, Block << h) => Label -> TL t h (Name a)
jmp lbl = sendR (Jmp lbl)