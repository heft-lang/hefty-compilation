{-# OPTIONS_GHC -Wno-tabs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
import Data.Bool (bool)
{-# HLINT ignore "Use newtype instead of data" #-}

data Id

data Cmd 
	= CFn Fn
	| Dummy
	| Seq Cmd Cmd
	| CIf Exp Cmd Cmd
	| While Exp Cmd
	| Goto Exp
	| Block Cmd [(Id, Cmd)]
	| Resultis Exp

data Exp
	= EId Id
	| ETrue
	| EFalse
	| EIf Exp Exp Exp
	| Valof Cmd

data Fn

-- machine states / stores
data S

data C = C (S -> S)

data T = FF | TT

data D

data Env = Env (Id -> D)

c :: Cmd -> Env -> C
c = _

lookupC :: Env -> Id -> S -> S
lookupC _ _ = _

p :: Cmd -> Env -> C -> S -> S
p (Goto (EId x)) r k s = lookupC r x s
p _ r k s = _

-- expression results
data E

te :: T -> E
te _ = _

eBool :: E -> Bool
eBool _ = _

-- expression continuation
data K = K { appK :: E -> S -> S }

lookupE :: Env -> Id -> E
lookupE _ _ = _

e :: Exp -> Env -> K -> S -> S
e ETrue r k s = appK k (te TT) s
e EFalse r k s = appK k (te FF) s
e (EId x) r k s = appK k (lookupE r x) s
e (EIf e0 e1 e2) r k s = e e0 r (K (bool (e e1 r k) (e e2 r k) . eBool)) s
e (Valof c) r k s = _