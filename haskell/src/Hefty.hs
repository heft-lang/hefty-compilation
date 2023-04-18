{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda" #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-} -- needed for 'type Effect' in GHC 9.2.5
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE BlockArguments #-}

module Hefty where

import Control.Monad
import Data.Type.Equality
import Data.Kind
import Unsafe.Coerce (unsafeEqualityProof, UnsafeEquality (UnsafeRefl))
import Data.Bifunctor (first)
import Control.Category (Category (..))
import Prelude hiding ((.), id)
import Data.Functor.Compose

type Effect = (Type -> Type) -> (Type -> Type)

class HTraversable h where
  htraverse :: Applicative m => (forall x. Alpha x => f x -> m (g x)) -> h f a -> m (h g a)

hmap :: HTraversable h => (forall x. f x -> g x) -> h f a -> h g a
hmap f = unI . htraverse (I . f)

type HeftyS :: Effect -> Type -> Type
data HeftyS h a
  = ReturnS a
  | forall c. OpS (h (HeftyS h) (Name c)) (Name c) (HeftyS h a)

deriving instance (forall x. Show (h (HeftyS h) (Name x)), Show a) => Show (HeftyS h a)

deriving instance Functor (HeftyS h)
deriving instance Foldable (HeftyS h)
deriving instance Traversable (HeftyS h)

instance Applicative (HeftyS h) where pure = ReturnS; (<*>) = ap
instance Monad (HeftyS h) where
  ReturnS x >>= k = k x
  OpS op n k1  >>= k2 = OpS op n (k1 >>= k2)

infixr 6 ++
type (++) :: Effect -> Effect -> Effect
data (h1 ++ h2) f a = LH (h1 f a) | RH (h2 f a)
  deriving (Functor, Show)

instance (HTraversable f, HTraversable g) => HTraversable (f ++ g) where
  htraverse f (LH x) = LH <$> htraverse f x
  htraverse f (RH x) = RH <$> htraverse f x

sumH_ :: (h1 f a -> b) -> (h2 f a -> b) -> (h1 ++ h2) f a -> b
sumH_ f _ (LH x) = f x
sumH_ _ g (RH x) = g x

-- hfunctor subsumption

newtype (:~~>) h1 h2 = NTH { ($$$) :: forall f x. h1 f x -> h2 f x }

instance Category (:~~>) where
  id = NTH id
  (.) (NTH f) (NTH g) = NTH (f . g)

data (<~~>) f g = IsoH { toH :: f :~~> g, fromH :: g :~~> f }

(<~~>) :: (f :~~> g) -> (g :~~> f) -> f <~~> g
(<~~>) = IsoH

isoReflH :: f <~~> f
isoReflH = id <~~> id

isoSymH :: f <~~> g -> g <~~> f
isoSymH iso = fromH iso <~~> toH iso

isoTransH :: f <~~> g -> g <~~> h -> f <~~> h
isoTransH iso1 iso2 = (toH iso2 . toH iso1) <~~> (fromH iso1 . fromH iso2)

isoSumCongH :: g <~~> h -> (f ++ g) <~~> (f ++ h)
isoSumCongH iso = NTH (sumH_ LH (RH . ($$$) (toH iso)))
             <~~> NTH (sumH_ LH (RH . ($$$) (fromH iso)))

isoSumSwapH :: (f ++ (g ++ h)) <~~> (g ++ (f ++ h))
isoSumSwapH = NTH (sumH_ (RH . LH) (sumH_ LH (RH . RH)))
         <~~> NTH (sumH_ (RH . LH) (sumH_ LH (RH . RH)))


-- injection/toFore pack,
-- which existentially packages `h` and a witness that `g <~~> f ++ h`
data ForephismH f g =
  forall h. ForephismH { forephismH :: g <~~> (f ++ h) }


-- functor subsumption

infixr 5 <<
class f << g where
  witnessH :: ForephismH f g

-- short-hand

injH :: forall h1 h2 c f a. h1 << h2 => h1 f a -> h2 f a
injH x = case witnessH @h1 @h2 of
  ForephismH iso -> fromH iso $$$ LH x

projH :: forall h1 h2 c f a. h1 << h2 => h2 f a -> Maybe (h1 f a)
projH x = case witnessH @h1 @h2 of
  ForephismH iso -> sumH_ Just (const Nothing) $ toH iso $$$ x

-- sum instances

data NopH m a

unH :: HeftyS NopH a -> a
unH (ReturnS x) = x
unH (OpS op _ _) = case op of

-- nopAlg :: Alg NopH f
-- nopAlg = Alg \case

instance {-# OVERLAPPING #-} h << h where
  witnessH = ForephismH (NTH LH <~~> NTH (sumH_ id (\(x :: NopH f k) -> case x of)))

instance {-# OVERLAPPING #-} f << f ++ g where
  witnessH :: ForephismH f (f ++ g)
  witnessH = ForephismH isoReflH

instance (f << g) => f << h ++ g where
  witnessH = case witnessH @f @g of
    ForephismH iso ->
      ForephismH (isoTransH (isoSumCongH iso) isoSumSwapH)


-- newtype Alg h g = Alg { alg :: forall x a. h g x -> (x -> g a) -> g a }
-- 
-- infixr ++~
-- (++~) :: Alg h1 g -> Alg h2 g -> Alg (h1 ++ h2) g
-- a1 ++~ a2 = Alg \case
--   LH x -> alg a1 x
--   RH x -> alg a2 x
-- 
-- injAlg :: h << g => Alg h (HeftyS g)
-- injAlg = Alg (OpS . injH)

newtype I a = I { unI :: a } deriving (Show, Functor)
instance Applicative I where
  pure = I
  I f <*> I x = I (f x)

type Name :: Type -> Type
newtype Name a = Name Int deriving Show
type role Name nominal

-- Day (Freer f) (HeftyS g) a = (Freer f b, HeftyS g c, b -> c -> a)
-- TL f g a = Freer f (HeftyS g a)
newtype TL f g a = TL { unTL :: Freer f (HeftyS g a) }
instance Functor (TL f g) where
  fmap = liftM
instance Applicative (TL f g) where
  pure = TL . pure . pure
  (<*>) = ap

instance Monad (TL f g) where
  TL m >>= k = TL $ do
    t <- m
    t' <- unTL (k (extract t))
    pure (append t t')

extract :: HeftyS f a -> a
extract (ReturnS x) = x
extract (OpS _ _ k) = extract k

-- Not hygenic!
append :: HeftyS f a -> HeftyS f b -> HeftyS f b
append (ReturnS _) y = y
append (OpS op n k) y = OpS op n (append k y)

flush :: TL f g a -> TL f g' (HeftyS g a)
flush (TL m) = TL (fmap pure m)

data Freer f a = Pure a | forall x. Freer (f (I x)) (I x -> Freer f a)

instance Functor (Freer f) where
  fmap = liftM
instance Applicative (Freer f) where
  pure = Pure
  (<*>) = ap
instance Monad (Freer f) where
  Pure x >>= k = k x
  Freer op k >>= k' = Freer op (k >=> k')

eqName :: forall x y. Name x -> Name y -> Maybe (x :~: y)
eqName (Name x) (Name y)
  | x == y = case unsafeEqualityProof @x @y of UnsafeRefl -> Just Refl
  | otherwise = Nothing

class Alpha a where
  rename :: Name b -> Name b -> a -> a
instance Alpha (Name a) where
  rename x y z =
    case eqName x z of
      Just Refl -> y
      Nothing -> z
instance (forall m x. (forall y. Alpha y => Alpha (m y)) => Alpha (f m x), Alpha a) => Alpha (HeftyS f a) where
  rename x y (ReturnS z) = ReturnS (rename x y z)
  rename x y (OpS op n k) = OpS (rename x y op) (rename x y n) (rename x y k)

instance Alpha () where
  rename _ _ () = ()

instance Alpha Int where
  rename _ _ = id
instance Alpha Bool where
  rename _ _ = id
instance Alpha a => Alpha [a] where
  rename x y = map (rename x y)
instance Alpha Char where
  rename _ _ = id
instance (Alpha a, Alpha b) => Alpha (a, b) where
  rename x y (l, r) = (rename x y l, rename x y r)

data (f + g) x = L (f x) | R (g x)

instance (Alpha (f a), Alpha (g a)) => Alpha ((f + g) a) where
  rename x y (L z) = L (rename x y z)
  rename x y (R z) = R (rename x y z)

instance (Alpha (f m a), Alpha (g m a)) => Alpha ((f ++ g) m a) where
  rename x y (LH z) = LH (rename x y z)
  rename x y (RH z) = RH (rename x y z)

class f < g where
  inj :: f a -> g a

instance {-# OVERLAPPING #-} f < (f + h) where
  inj = L

instance f < h => f < (g + h) where
  inj = R . inj

data Fresh a where
  Fresh :: Fresh (I (Name a))

hFresh :: TL (Fresh + f) g a -> TL f g a
hFresh = handleC id (const lift) (0 :: Int) $ \p op k ->
  case op of
    Fresh -> k (p + 1) (I (Name p))

handleC :: (forall x. g x -> h x) -> (p -> HeftyS t a -> TL h t b) -> p -> (forall x. p -> f x -> (p -> x -> TL h t b) -> TL h t b) -> TL (f + g) t a -> TL h t b
handleC sub gen p alg = go p . unTL where
  go p (Pure x) = gen p x
  go p (Freer op k) =
    case op of
      L op' -> alg p op' (\p x -> go p $ k x)
      R op' -> TL (Freer (sub op') (unTL . go p . k))

weakenC :: TL g h a -> TL (f + g) h a
weakenC = TL . weakenFreer . unTL

weakenFreer :: Freer g a -> Freer (f + g) a
weakenFreer (Pure x) = Pure x
weakenFreer (Freer op k) = Freer (R op) (weakenFreer . k)

sendC :: f < g => f (I a) -> TL g h (I a)
sendC x = TL (Freer (inj x) (pure . pure))

weakenR :: forall f g h a. HTraversable h => (forall m x. g m x -> h m x) -> TL f g a -> TL f h a
weakenR sub m = do
  x <- flush m
  lift (go x)
  where
    go :: HeftyS g b -> HeftyS h b
    go x = case x of
      ReturnS x -> ReturnS x
      OpS op v k -> OpS (hmap go (sub op)) v (go k)

sendR :: (Fresh < g, f << h) => f (HeftyS h) (Name a) -> TL g h (Name a)
sendR x = do I n <- sendC Fresh; TL (pure (OpS (injH x) n (ReturnS n)))

sendSubR :: (Fresh < g) => (forall m x. f m x -> h m x) -> f (HeftyS h) (Name a) -> TL g h (Name a)
sendSubR sub x = do I n <- sendC Fresh; TL (pure (OpS (sub x) n (ReturnS n)))

type AlphaEffect :: Effect -> Constraint
type AlphaEffect f = forall m x. (forall y. Alpha y => Alpha (m y)) => Alpha (f m x)

handleM :: forall a h g f t. (Alpha a, AlphaEffect f, AlphaEffect g, HTraversable f, HTraversable g) =>
  (forall m x. g m x -> h m x) ->
  (forall x. x -> TL t h x) ->
  (forall x y. f (HeftyS h) (Name x) -> (Name x -> TL t h y) -> TL t h y) ->
  TL t (f ++ g) a -> TL t h a
handleM sub gen alg = flush >=> go where
  go :: forall x. Alpha x => HeftyS (f ++ g) x -> TL t h x
  go (ReturnS x) = gen x
  go (OpS op n k) =
    case op of
      LH op' -> htraverse (flush . go) op' >>= \op'' -> alg op'' (\n' -> go (rename n n' k))
      RH op' -> htraverse (flush . go) op' >>= \op'' -> hoist (OpS (sub op'') n) (go k)

hoist :: (forall x. HeftyS g x -> HeftyS h x) -> TL f g a -> TL f h a
hoist f (TL x) = TL (f <$> x)

-- type TraverseU :: ((Type -> Type) -> Effect) -> Constraint
-- class TraverseU f where
--   traverseU :: Applicative m => (forall x. c x -> m (c' x)) -> f c n (c a) -> m (f c' n (c' a))

-- instance TraverseU Arith where
--   traverseU _ (Int x) = pure (Int x)
--   traverseU f (Plus x y) = Plus <$> f x <*> f y

-- unquote :: forall f. TraverseU f => TL End (f Name) () -> Freer (f I) ()
-- unquote (TL (Pure t)) = go (\_ -> error "scope error") t where
--   go :: (forall x. Name x -> I (I x)) -> HeftyS (f Name) () -> Freer (f I) ()
--   go _ (ReturnS ()) = Pure ()
--   go f (OpS op n k) = Freer (unI $ traverseU f op) (\x -> go (\n' -> case eqName n n' of Just Refl -> I x; Nothing -> f n') k)
-- unquote (TL (Freer op _)) = case op of

lift :: HeftyS h a -> TL t h a
lift = TL . Pure

data Nil a
data NilH m a

nilTL :: TL Nil NilH a -> a
nilTL (TL (Pure (ReturnS x))) = x