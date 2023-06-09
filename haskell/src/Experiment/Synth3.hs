{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE IncoherentInstances #-}

module Experiment.Synth where

import Control.Monad.State
import Unsafe.Coerce
import Data.Maybe


{- UNIVERSE OF TYPE UNIVERSAL TYPES -}

type Univ = * -> *

type PSet = Univ -> *

newtype A (p :: PSet) = A { unA :: forall u. p u }

newtype In x (u :: Univ) = In { unIn :: u x }

newtype (p ==> p') u = Arr { unArr :: p u -> p' u }

class UFunctor0 f where
  umap :: A( p ==> p' ) -> A( f p ==> f p' )


{- MORPHISMS BETWEEN UNIVERSES OF TYPE UNIVERSE PARAMETERIZED -}

type QSet = Univ -> Univ -> *

newtype A2 (q :: QSet) = A2 { unA2 :: forall u t. q u t }

newtype (p ->> p') u t = ArrP { unArrP :: p u -> p' t }

infixr 6 =>>
newtype (q =>> q') u t = Arr2 { unArr2 :: q u t -> q' u t }

class UMFunctor0 f where
  ummap0 :: (a -> b) -> A2( f a ->> f b )


{- HIGHER-ORDER FUNCTORS OVER UMs -}

newtype (f ~~> f') (u :: Univ) (t :: Univ)
  = ArrA { unArrA :: forall a. f a u -> f' a t }
--  = ArrA { unArrA :: forall a. (f a ->> f' a) u t }

class (forall f. UMFunctor0 (h f)) => HUMFunctor0 h where
  hummap0 :: A2( (f ~~> f') =>> (h f ~~> h f') )

data Hefty0 h a :: PSet where
  Pure0 :: u a                           -> Hefty0 h a u
  Op0   :: h (Hefty0 h) (Hefty0 h a u) u -> Hefty0 h a u

-- Hefty lives in the universe of type universal types
pure0_ :: A( In a ==> Hefty0 h a )
pure0_ = A $ Arr $ \ (In x) -> Pure0 x

-- op_ :: A( h (Hefty0 h) (Hefty0 h a) ==> Hefty0 h a )
-- op_ = A $ Arr Op0


{- FOLD -}

data (Gen (g :: * -> PSet))
       (u :: Univ)
       (t :: Univ)
  = Gen { runGen :: forall c. (In c ->> g c) u t }

data (Alg0 (h :: (* -> PSet) -> (* -> PSet))
           (g :: * -> PSet))
       (u :: Univ)
       (t :: Univ)
  = Alg0 { runAlg0 :: forall a. h g (g a t) t -> g a t }

hfold0 :: forall g h a.
          HUMFunctor0 h
       => A2(   Gen g
              =>> Alg0 h g
              =>> (Hefty0 h a ->> g a) )
hfold0 = A2 $ Arr2 $ \g -> Arr2 $ \a -> ArrP $ \h -> case h of
  Pure0 x -> unArrP (runGen g) (In x)
  Op0 f   ->
    (runAlg0 a)
    (unArrA
      ((unArr2 (unA2 (hummap0 @h)))
       (ArrA $ unArrP (unArr2 (unArr2 (unA2 hfold0) g) a)))
      (unArrP (unA2 (ummap0 (unArrP (unArr2 (unArr2 (unA2 hfold0) g) a)))) f))


-- unfolding newtypes and reordering arguments a bit:

data Hefty h (u :: Univ) a
  = Pure (u a)
  | Op (h (Hefty h) u (Hefty h u a))

class (forall f u. Functor (h f u)) => HUMFunctor h u t where
  hummap :: forall (f :: Univ -> * -> *) (f' :: Univ -> * -> *).
            (forall a. f u a -> f' t a)
         -> (forall a. h f u a -> h f' t a)

data Alg (h :: (Univ -> * -> *) -> (Univ -> * -> *)) (g :: Univ -> * -> *) u
  = Alg { runAlg :: forall a. h g u (g u a) -> g u a }

hfold :: forall g h a u t.
         HUMFunctor h u t
      => (forall c. u c -> g t c)
      -> Alg h g t
      -> Hefty h u a
      -> g t a
hfold gen a (Pure x) = gen x
hfold gen a (Op f)   = runAlg a $ hummap (hfold gen a) (fmap (hfold gen a) f)


{- GENERALIZED FOLD -}

data AlgG h (g :: Univ -> * -> *) t a = AlgG { algG :: h g t a -> a }

gfold :: forall g h a b u t.
         HUMFunctor h u t
      => (forall c. u c -> g t c)
      -> Alg h g t
      -> (u a -> b)
      -> AlgG h g t b
      -> Hefty h u a
      -> b
gfold _    _  gen2 _  (Pure x) = gen2 x
gfold gen1 a1 gen2 a2 (Op f)   = algG a2 $ hummap (hfold gen1 a1) (fmap (gfold gen1 a1 gen2 a2) f)



{- DENOTABLE H.O. FUNCTOR SUM -}

infixr 6 +
data (h1 + h2) (to :: * -> * -> *) (f :: Univ -> * -> *) (u :: Univ) a
  = L (h1 to f u a)
  | R (h2 to f u a)
  deriving Functor

deriving instance ( Foldable (h1 Synt f Namy)
                  , Foldable (h2 Synt f Namy) ) => Foldable ((h1 + h2) Synt f Namy)
deriving instance ( Traversable (h1 Synt f Namy)
                  , Traversable (h2 Synt f Namy) ) => Traversable ((h1 + h2) Synt f Namy)

instance (HUMFunctor (h1 to) u t, HUMFunctor (h2 to) u t) => HUMFunctor ((h1 + h2) to) u t where
  hummap f (L x) = L $ hummap f x
  hummap f (R x) = R $ hummap f x


{- FUNCTOR COMPOSITION, ID FUNCTOR, AND CONST FUNCTOR -}

infixr 6 :$:
newtype (f :$: g) (u :: Univ) a = Comp { unComp :: f (g u a) }
  deriving Functor

deriving instance Show (f (g u a)) => Show ((f :$: g) u a)

newtype Id a = Id { unId :: a } deriving Functor

instance Show x => Show (Id x) where
  show = show . unId 

instance Applicative Id where
  pure = Id
  Id f <*> Id x = Id $ f x

instance Monad Id where
  Id x >>= k = k x

newtype Const (a :: *) (b  :: *) = Const { unConst :: a }

instance Show (Const String a) where
  show = unConst

newtype UConst (a :: *) (b :: Univ) (c :: *) = UConst { unUConst :: a }

instance Show (UConst String u c) where
  show = unUConst


{- NAMING INFRASTRUCTURE -}

data Synt a b
  = Dot { par :: String, bod :: b } deriving (Functor, Foldable, Traversable)

type Namy = Const String

instance Show b => Show (Synt a b) where
  show (Dot s b) = "(λ " ++ s ++ ". " ++ show b ++ ")"

instance Show (Synt a String) where
  show (Dot s b) = "(λ " ++ s ++ ". " ++ b ++ ")"

instance ( HUMFunctor (h Synt) Namy Namy
         , Show (h Synt (UConst String) Namy String) )
       => Show (Hefty (h Synt) Namy a) where
  show = unUConst . hfold
    (\ (Const x) -> UConst x)
    (Alg $ \ m -> UConst $ show $ fmap unUConst $ hummap @_ @Namy id m)
    

instance ( Show (h1 Synt (UConst String) Namy String)
         , Show (h2 Synt (UConst String) Namy String) )
      => Show ((h1 + h2) Synt (UConst String) Namy String) where
  show (L x) = show x
  show (R x) = show x


{- TRAVERSABLE -}

class HUMTraversable (h :: (Univ -> * -> *) -> (Univ -> * -> *)) u t m where
  humtraverse :: (forall a. f u a -> m (g t a))
              -> h f u a
              -> m (h g t a)

instance {-# OVERLAPPING #-}
         ( forall f u. Functor (h Synt f u)
         , HUMTraversable (h Synt) Namy Namy Id ) => HUMFunctor (h Synt) Namy Namy where
  hummap f = unId . humtraverse (Id . f)

instance ( Functor m
         , HUMTraversable (h1 to) u t m
         , HUMTraversable (h2 to) u t m ) => HUMTraversable ((h1 + h2) to) u t m where
  humtraverse f (L x) = L <$> humtraverse f x
  humtraverse f (R x) = R <$> humtraverse f x


{- MONAD -}

-- but not in Hask

class UMApplicative f where
  umpure :: t a -> f t a
  (<&&>) :: f t a -> f t b -> f t (a, b)

pur = Pure

(>>=) :: HUMFunctor h u u => Hefty h u a -> (u a -> Hefty h u b) -> Hefty h u b
m >>= k = gfold Pure (Alg Op) k (AlgG Op) m

-- instance HUMFunctor h => Applicative (Hefty h u) where pure = Pure; (<*>) = ap
-- instance HUMFunctor h => Functor (Hefty h u) where fmap = liftM
-- instance HUMFunctor h => Monad (Hefty h u) where
--   m >>= k = gfold Pure (Alg Op) k (AlgG Op) m


{- SYNTACTIFICATION -}

class Syntactic h where
  syntactify :: h (->) f Namy k -> State Int (h Synt f Namy k)

instance (Syntactic h1, Syntactic h2) => Syntactic (h1 + h2) where
  syntactify (L x) = L <$> syntactify x
  syntactify (R x) = R <$> syntactify x

fresh :: State Int String
fresh = do
  i <- get
  put (i + 1)
  return $ "x" ++ show i

toSyntax :: ( Syntactic h
            , HUMTraversable (h Synt) Namy Namy (State Int)
            , forall f. Traversable (h Synt f Namy)
            , HUMFunctor (h (->)) Namy Namy )
         => Hefty (h (->)) Namy a
         -> Hefty (h Synt) Namy a
toSyntax = fst . ($ 0) . runState . unComp . hfold
  (Comp . pure . Pure)
  (Alg $ \ m -> Comp $ Op <$> do
      m1 <- syntactify m
      m2 <- humtraverse unComp m1
      traverse unComp m2)


{- SEMANTIFICATION -}

data Pack t = forall x. Pack { unpack :: t x }

instance (forall x. Show (t x)) => Show (Pack t) where
  show (Pack x) = show x

type Envy u = (->) [(String, Pack u)]

class Semantic h where
  semantify :: h Synt (Envy u :$: f) u ([(String, Pack u)] -> k)
            -> [(String, Pack u)]
            -> h (->) f u k

instance (Semantic h1, Semantic h2) => Semantic (h1 + h2) where
  semantify (L x) = L . semantify x
  semantify (R x) = R . semantify x

look :: [(String, Pack t)] -> String -> Pack t
look r = fromJust . flip lookup r

toSemantix :: ( Semantic h
              , HUMFunctor (h Synt) Namy t )
           => Hefty (h Synt) Namy a
           -> Hefty (h (->)) t a
toSemantix = ($ []) . unComp . hfold
  (\ (Const x) -> Comp $ \r -> Pure $ case look r x of Pack v -> unsafeCoerce v)
  (Alg $ \ m -> Comp $ \r -> Op $ semantify (fmap unComp m) r)



{- NORMALIZABLE -}

-- A given monad can be used to normalize things in u to things in t

class Normalizable u m t where
  normalize :: u x -> m (t x)

instance Normalizable Namy (Envy u) u where
  normalize (Const x) = \r -> case look r x of Pack v -> unsafeCoerce v

instance {-# OVERLAPPING #-} Applicative m => Normalizable u m u where
  normalize = pure

-- {- ARITH OP -}

data Arith to m u k
  = Num Int (u Int `to` k)
  | Plus (u Int) (u Int) (u Int `to` k)

deriving instance (forall a. Functor (to a)) => Functor (Arith to u m)
deriving instance Show (Arith Synt (UConst String) Namy String)
deriving instance Foldable (Arith Synt f Namy)
deriving instance Traversable (Arith Synt f Namy)

instance Functor (Envy u) where fmap f x r = f (x r)
instance Applicative (Envy u) where
  pure x r = x
  (fg <*> fy) r = fg r (fy r)
instance Monad (Envy u) where
  (m >>= k) r = k (m r) r

instance ( Normalizable Namy m u
         , Monad m )
      => HUMTraversable (Arith Synt) Namy u m where
  humtraverse f (Num i (x `Dot` k)) = pure $ Num i (x `Dot` k)
  humtraverse f (Plus v1 v2 (x `Dot` k)) = do
    v1' <- normalize v1
    v2' <- normalize v2
    pure $ Plus v1' v2' (x `Dot` k)

instance {-# OVERLAPPING #-} HUMFunctor (Arith (->)) u u where
  hummap f (Num i k) = Num i k
  hummap f (Plus v1 v2 k) = Plus v1 v2 k

instance Syntactic Arith where
  syntactify (Num i k) = do
    x <- fresh
    pure $ Num i (x `Dot` k (Const x))
  syntactify (Plus i1 i2 k) = do
    x <- fresh
    pure $ Plus i1 i2 (x `Dot` k (Const x))

instance Semantic Arith where
  semantify (Num i (x `Dot` k)) r =
    Num i (\ w -> k ((x, Pack w):r))
  semantify (Plus x y (z `Dot` k)) r =
    Plus x y
      (\ w -> k ((z, Pack w):r))


{- LET OP -}

data Let to (m :: Univ -> * -> *) (u :: Univ) k
  = forall a b. Let (u a) (u a `to` m u b) (u b `to` k)

deriving instance (forall a. Functor (to a)) => Functor (Let to u m)
deriving instance Show (Let Synt (UConst String) Namy String)
deriving instance Foldable (Let Synt f Namy)
deriving instance Traversable (Let Synt f Namy)

-- instance (forall a. Functor (to a), forall t. Show (u t)) => HFunctor (Let to u) where
--   hmap f (Let v body k) = Let v (fmap f body) k

instance ( Normalizable Namy m u
         , Monad m )
      => HUMTraversable (Let Synt) Namy u m where
  humtraverse f (Let v (x `Dot` body) (y `Dot` k)) = do
    v' <- normalize v
    body' <- f body
    pure $ Let v' (x `Dot` body') (y `Dot` k)
    -- \r ->
    -- Let
    --   (case look r v of Pack x -> unsafeCoerce x)
    --   (x `Dot` f body r)
    --   (y `Dot` k)

instance {-# OVERLAPPING #-} HUMFunctor (Let (->)) u u where
  hummap f (Let v m k) = Let v (f . m) k

instance Syntactic Let where
  syntactify (Let v body k) = do
    x1 <- fresh
    x2 <- fresh
    pure $ Let v (x1 `Dot` body (Const x1)) (x2 `Dot` k (Const x2))

instance Semantic Let where
  semantify (Let v (y `Dot` body) (z `Dot` k)) r =
    Let
      v
      (\ w -> unComp body ((y, Pack w):r))
      (\ w -> k ((z, Pack w):r))


{- TEST -}

prog :: Hefty ((Arith + Let) (->)) u Int
prog = Op $ L $ Num 42 $ \ x ->
  Op $ R $ Let x
    (\ v -> Op $ L $ Plus x v Pure)
    Pure

-- λ> toSyntax (toSemantix (toSyntax prog))
-- Num 42 (λ x0. Let x0 (λ x1. Plus x0 x1 (λ x3. x3)) (λ x2. x2))

