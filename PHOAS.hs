{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

import Control.Monad
import Data.Monoid (Sum)

data Lam = Var Int | Lam Int Lam | App Lam Lam 

data LamAlg a = MkLamAlg
  { var :: Int -> a
  , lam :: Int -> a -> a
  , app :: a -> a -> a
  }

cataLam :: LamAlg a -> Lam -> a
cataLam alg (Var i)   = var alg i 
cataLam alg (Lam i x) = lam alg i (cataLam alg x)
cataLam alg (App x y) = app alg (cataLam alg x) (cataLam alg y)

countVars :: Lam -> Int
countVars = cataLam MkLamAlg
  { var = \_ -> 1
  , lam = \_ x -> x
  , app = \x y -> x + y
  }

data Writer w a = MkWriter w a deriving Functor
instance Monoid w => Applicative (Writer w) where
  pure = MkWriter mempty
  (<*>) = ap
instance Monoid w => Monad (Writer w) where
  MkWriter w1 x >>= f = let MkWriter w2 y = f x in MkWriter (w1 <> w2) y

tell :: w -> Writer w ()
tell w = MkWriter w ()

countVarsM :: Lam -> Writer (Sum Int) Lam
countVarsM = cataLam MkLamAlg
  { var = \n -> tell 1 >> pure (Var n)
  , lam = \n x -> x >>= \x' -> pure (Lam n x')
  , app = \x y -> x >>= \x' -> y >>= \y' -> pure (App x' y')
  }

data LamP p = VarP p | LamP (p -> LamP p) | AppP (LamP p) (LamP p)
newtype LamPI = MkLamPI { unLamPI :: LamP Int }

pattern VarPI :: Int -> LamPI
pattern VarPI p = MkLamPI (VarP p)

pattern LamPI :: LamPI -> LamPI
pattern LamPI x <- MkLamPI (LamP (MkLamPI . ($ error "This shouldn't be used") -> x)) where
  LamPI (MkLamPI x) = MkLamPI (LamP (\_ -> x))

pattern AppPI :: LamPI -> LamPI -> LamPI
pattern AppPI x y <- MkLamPI (AppP (MkLamPI -> x) (MkLamPI -> y)) where
  AppPI (MkLamPI x) (MkLamPI y) = MkLamPI (AppP x y)

{-# COMPLETE VarPI, LamPI, AppPI #-}

data LamPAlg p a = MkLamPAlg
  { varp :: p -> a
  , lamp :: (p -> a) -> a
  , appp :: a -> a -> a
  }

cataLamP :: LamPAlg p a -> LamP p -> a
cataLamP MkLamPAlg {..} = go where
  go (VarP p) = varp p
  go (LamP f) = lamp (go . f)
  go (AppP x y) = appp (go x) (go y)

p2p :: (forall p. LamP p) -> (forall p. LamP p)
p2p x0 = cataLamP MkLamPAlg {..} x0 [] where
  varp n xs = VarP (xs !! n)
  lamp f xs = LamP (\x -> f (length xs) (xs ++ [x]))
  appp x y xs = AppP (x xs) (y xs)

p2i :: (forall p. LamP p) -> LamPI
p2i x0 = cataLamP MkLamPAlg {..} x0 0 where
  varp p _ = VarPI p
  lamp f n = LamPI (f n (n + 1))
  appp x y n = AppPI (x n) (y n)

i2p :: LamPI -> (forall p. LamP p)
i2p (MkLamPI x0) = cataLamP MkLamPAlg {..} x0 [] where
  varp n xs = VarP (xs !! n)
  lamp f xs = LamP (\x -> f (error "This shouldn't be used") (xs ++ [x]))
  appp x y xs = AppP (x xs) (y xs)

data LamPIAlg a = MkLamPIAlg
  { varpi :: Int -> a
  , lampi :: a -> a
  , apppi :: a -> a -> a
  }

cataLamPI :: LamPIAlg a -> (forall p. LamP p) -> a
cataLamPI MkLamPIAlg {..} x0 = go (p2i x0) where
  go (VarPI i) = varpi i
  go (LamPI x) = lampi (go x)
  go (AppPI x y) = apppi (go x) (go y)

-- countVarsMP :: (forall p. LamP p) -> Writer (Sum Int) (forall p. LamP p)
-- countVarsMP x0 = i2p <$> cataLamP MkLamPAlg {..} x0 0 where
--   varp n _ = tell 1 >> pure (VarPI n)
--   lamp f n = f n (n + 1) >>= \f' -> pure (LamPI f')
--   appp x y n = x n >>= \x' -> y n >>= \y' -> pure (AppPI x' y')

countVarsMP :: (forall p. LamP p) -> Writer (Sum Int) (forall p. LamP p)
countVarsMP = fmap i2p . cataLamPI MkLamPIAlg {..} where
  varpi n = tell 1 *> pure (VarPI n)
  lampi x = LamPI <$> x
  apppi x y = AppPI <$> x <*> y

countVarsMP' :: (forall p. LamP p) -> Int
countVarsMP' x0 = cataLamP MkLamPAlg {..} x0 where
  varp () = 1
  lamp f = f ()
  appp x y = x + y

fromP :: (forall p. LamP p) -> Lam
fromP x0 = go 0 x0 where
  go _   (VarP n) = Var n
  go n (LamP f) = Lam n (go (n + 1) (f n))
  go n (AppP x y) = App (go n x) (go n y)

type Env p = Int -> Maybe p

emptyEnv :: Env p
emptyEnv = const Nothing

lookupEnv :: Env p -> Int -> Maybe p
lookupEnv = id
--   case (f x) of
--     Just y -> y
--     Nothing -> error "Scope error"

insertEnv :: Env p -> Int -> p -> Env p
insertEnv f n x m
  | n == m = Just x
  | otherwise = f m

-- toP :: Lam -> Maybe (LamP p)
-- toP x0 = fmap ($ undefined) (go x0 emptyEnv) where
--   go :: Lam -> Env p -> Maybe (p -> LamP p)
--   go (Var n) = \env -> const VarP <$> lookupEnv env n
--   go (Lam n x) = \env ->
--     go x (insertEnv env n _) >>= \x' -> pure (\_ -> LamP x')
--   go (App x y) = \env -> (\x y p -> AppP (x p) (y p)) <$> go x env <*> go y env
--

-- p2p :: (forall p. LamP p) -> (forall p. LamP p)
-- p2p x0 = go [] x0 where
--   go :: [p] -> LamP Int -> LamP p
--   go xs (VarP n) = VarP (xs !! n)
--   go xs (LamP f) = LamP (\x -> go (xs ++ [x]) (f (length xs)))
--   go xs (AppP x y) = AppP (go xs x) (go xs y)
