{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE IncoherentInstances #-}

module Experiment.Synth where

import Control.Monad.State
import Unsafe.Coerce
import Data.Maybe


{- HEFTY -}

data Hefty h a
  = Pure a
  | Op (h (Hefty h) (Hefty h a))


{- FOLD -}

type f ~> g = forall a. f a -> g a

class (forall f. Functor (h f)) => HFunctor h where
  hmap :: (f ~> g) -> h f ~> h g


data Alg h g = Alg { alg :: forall a. h g (g a) -> g a }

hfold :: forall g h a.
         HFunctor h
      => (forall c. c -> g c)
      -> Alg h g
      -> Hefty h a
      -> g a
hfold gen _ (Pure a) = gen a
hfold gen a (Op f)   = alg a $ hmap (hfold gen a) (fmap (hfold gen a) f)


{- MENDLER-STYLE FOLD -}

data AlgM h g = AlgM { algM :: forall x f. (f ~> g) -> h f (f x) -> g x }

mfold :: (forall x. x -> g x)
      -> AlgM h g
      -> Hefty h a
      -> g a
mfold gen _ (Pure a) = gen a
mfold gen a (Op f) = algM a (mfold gen a) f


-- Mendler-style fold for nested functor

data AlgTM h t g u = AlgTM { algTM :: forall x f. (forall y. f (t y) -> g (u y)) -> h f (f (t x)) -> g (u x) }

mtfold :: (forall x. t x -> g (u x))
       -> AlgTM h t g u
       -> Hefty h (t a) -- nested
       -> g (u a)       -- nested
mtfold gen _ (Pure a) = gen a
mtfold gen a (Op f) = algTM a (mtfold gen a) f


{- GENERALIZED FOLD -}

data AlgG h (g :: * -> *) a = AlgG { algG :: h g a -> a }

gfold :: forall g h a b.
         HFunctor h
      => (forall c. c -> g c)
      -> Alg h g
      -> (a -> b)
      -> AlgG h g b
      -> Hefty h a
      -> b
gfold _    _  gen2 _  (Pure x) = gen2 x
gfold gen1 a1 gen2 a2 (Op f)   = algG a2 $ hmap (hfold gen1 a1) $ fmap (gfold gen1 a1 gen2 a2) f


{- MENDLER-STYLE HIGHER-ORDER TRAVERSABLE -}

class HTraversableM h where
  htraverseM :: Applicative m
             => (f ~> (m :$: g))
             -> h f (f x)
             -> m (h g (g x))


-- Mendler-style higher-order traversable for nested functor

class HTraversableTM h t where
  htraverseTM :: Applicative m
              => (forall x. f (t x) -> m (g (t x)))
              -> h f (f (t y))
              -> m (h g (g (t y)))


{- DENOTABLE H.O. FUNCTOR SUM -}

infixr 6 +
data (h1 + h2) (to :: * -> * -> *) (u :: * -> *) (f :: * -> *) a
  = L (h1 to u f a)
  | R (h2 to u f a)
  deriving Functor

instance (HFunctor (h1 to u), HFunctor (h2 to u)) => HFunctor ((h1 + h2) to u) where
  hmap f (L x) = L $ hmap f x
  hmap f (R x) = R $ hmap f x


{- FUNCTOR COMPOSITION, ID FUNCTOR, AND CONST FUNCTOR -}

infixr 6 :$:
newtype (f :$: g) a = Comp { unComp :: f (g a) }
  deriving (Functor, Show)

newtype Id a = Id { unId :: a } deriving Functor

instance Show x => Show (Id x) where
  show = show . unId 

instance Applicative Id where
  pure = Id
  Id f <*> Id x = Id $ f x

newtype Const (b :: *) (a  :: *) = Const { unConst :: b }

instance Show (Const String a) where
  show = unConst


{- NAMING INFRASTRUCTURE -}

data Synt a b
  = Dot { par :: String, bod :: b } deriving (Functor, Foldable, Traversable)

type Namy = Const String

instance Show b => Show (Synt a b) where
  show (Dot s b) = "(λ " ++ s ++ ". " ++ show b ++ ")"

instance Show (Synt a String) where
  show (Dot s b) = "(λ " ++ s ++ ". " ++ b ++ ")"

instance ( HFunctor (h Synt Namy)
         , HTraversableTM (h Synt Namy) Namy
         , Show (h Synt Namy Id String) )
       => Show (Hefty (h Synt Namy) (Namy a)) where
  show = unConst . unId . mtfold
    Id
    (AlgTM $ \ r m -> Id $ Const $ show $ fmap (unConst . unId) $ unId $ htraverseTM (Id . r) m)

instance ( Show (h1 Synt Namy Id String)
         , Show (h2 Synt Namy Id String) )
      => Show ((h1 + h2) Synt Namy Id String) where
  show (L x) = show x
  show (R x) = show x


{- MONAD -}

instance HFunctor h => Applicative (Hefty h) where pure = Pure; (<*>) = ap
instance HFunctor h => Functor (Hefty h) where fmap = liftM
instance HFunctor h => Monad (Hefty h) where
  m >>= k = gfold Pure (Alg Op) k (AlgG Op) m


{- SYNTACTIFICATION -}

class Syntactic h where
  syntactify :: h (->) Namy f k -> State Int (h Synt Namy f k)

instance (Syntactic h1, Syntactic h2) => Syntactic (h1 + h2) where
  syntactify (L x) = L <$> syntactify x
  syntactify (R x) = R <$> syntactify x

fresh :: State Int String
fresh = do
  i <- get
  put (i + 1)
  return $ "x" ++ show i
  
toSyntax :: ( Syntactic h
            , HTraversableTM (h Synt Namy) Namy )
         => Hefty (h (->) Namy) (Namy a)
         -> Hefty (h Synt Namy) (Namy a)
toSyntax = fst . ($ 0) . runState . unComp . mtfold
  (Comp . pure . Pure)
  (AlgTM $ \ r m -> Comp $ do
      m' <- syntactify m
      Op <$> htraverseTM (unComp . r) m')



{- SEMANTIFICATION -}

data Pack t = forall x. Pack { unpack :: t x }

instance (forall x. Show (t x)) => Show (Pack t) where
  show (Pack x) = show x

type Envy u = (->) [(String, Pack u)]

class Semantic h where
  semantify :: (forall x. f (Namy x) -> [(String, Pack u)] -> Hefty (h' (->) u) (u x))
            -> h Synt Namy f (f (Namy x))
            -> [(String, Pack u)]
            -> h (->) u (Hefty (h' (->) u)) (Hefty (h' (->) u) (u x))

instance (Semantic h1, Semantic h2) => Semantic (h1 + h2) where
  semantify r (L x) = L . semantify r x
  semantify r (R x) = R . semantify r x

look :: [(String, Pack t)] -> String -> Pack t
look r = fromJust . flip lookup r

toSemantix :: Semantic h
           => Hefty (h Synt Namy) (Namy a)
           -> Hefty (h (->) t) (t a)
toSemantix = flip
  (unComp . mtfold
    (\ (Const x) -> Comp $ \r -> Pure $ case look r x of Pack v -> unsafeCoerce v)
    (AlgTM $ \ r m -> Comp $ Op . semantify (fmap unComp r) m))
  []


{- ARITH OP -}

data Arith to u m k
  = Num Int (u Int `to` k)
  | Plus (u Int) (u Int) (u Int `to` k)

deriving instance (forall a. Functor (to a)) => Functor (Arith to u m)
deriving instance Show (Arith Synt Namy Id String)

instance (forall a. Functor (to a)) => HFunctor (Arith to u) where
  hmap _ (Num i k) = Num i k
  hmap _ (Plus i1 i2 k) = Plus i1 i2 k

instance HTraversableTM (Arith Synt Namy) Namy where
  htraverseTM r (Num i (x `Dot` k)) =
    (\ k' -> Num i (x `Dot` k'))
    <$> r k
  htraverseTM r (Plus v1 v2 (x `Dot` k)) =
    (\ k' -> Plus v1 v2 (x `Dot` k'))
    <$> r k

instance Syntactic Arith where
  syntactify (Num i k) = do
    x <- fresh
    pure $ Num i (x `Dot` k (Const x))
  syntactify (Plus i1 i2 k) = do
    x <- fresh
    pure $ Plus i1 i2 (x `Dot` k (Const x))

instance Semantic Arith where
  semantify r (Num i (x `Dot` k)) q =
    Num i (\ w -> r k ((x, Pack w):q))
  semantify r (Plus (Const x) (Const y) (z `Dot` k)) q =
    Plus
      (case look q x of Pack v -> unsafeCoerce v)
      (case look q y of Pack v -> unsafeCoerce v)
      (\ w -> r k ((z, Pack w):q))


{- LET OP -}

data Let to u m k
  = forall a b. Let (u a) (u a `to` m (u b)) (u b `to` k)

deriving instance (forall a. Functor (to a)) => Functor (Let to u m)
deriving instance Show (Let Synt Namy Id String)

instance (forall a. Functor (to a), forall t. Show (u t)) => HFunctor (Let to u) where
  hmap f (Let v body k) = Let v (fmap f body) k

instance HTraversableTM (Let Synt Namy) Namy where
  htraverseTM r (Let v (x `Dot` body) (y `Dot` k)) = 
   (\ body' k' -> Let v (x `Dot` body') (y `Dot` k'))
   <$> r body
   <*> r k

instance ( HTraversableTM (h1 to u) u
         , HTraversableTM (h2 to u) u ) => HTraversableTM ((h1 + h2) to u) u where
  htraverseTM r (L x) = L <$> htraverseTM r x
  htraverseTM r (R x) = R <$> htraverseTM r x

instance Syntactic Let where
  syntactify (Let v body k) = do
    x1 <- fresh
    x2 <- fresh
    pure $ Let v (x1 `Dot` body (Const x1)) (x2 `Dot` k (Const x2))

instance Semantic Let where
  semantify r (Let (Const x) (y `Dot` body) (z `Dot` k)) q =
    Let
      (case look q x of Pack v -> unsafeCoerce v)
      (\ w -> r body ((y, Pack w):q))
      (\ w -> r k ((z, Pack w):q))


{- TEST -}

prog :: Hefty ((Arith + Let) (->) u) (u Int)
prog = Op $ L $ Num 42 $ \ x ->
  Op $ R $ Let x
    (\ v -> Op $ L $ Plus x v Pure)
    Pure

-- λ> toSyntax (toSemantix (toSyntax prog))
-- Num 42 (λ x0. Let x0 (λ x1. Plus x0 x1 (λ x3. x3)) (λ x2. x2))

