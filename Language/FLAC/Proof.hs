{-# LANGUAGE GADTs, DataKinds, FlexibleContexts, RankNTypes, TypeInType, TypeOperators, TypeFamilies #-}

module Language.FLAC.Proof where

import Language.FLAC.Syntax
import Language.FLAC.Proof.ActsFor

import Data.Type.Map hiding (Var)
import Data.Proxy
import GHC.TypeLits

type Typed = Mapping Symbol Type

type family Subst (t :: Type) (x :: Symbol) (t' :: Type) :: Type where
  Subst ('TVar x) x t = t
  Subst ('Forall x p t) x _ = 'Forall x p t
  Subst ('Forall x p t) y t' = 'Forall x p (Subst t y t')
  Subst ('Plus t1 t2) x t' = 'Plus (Subst t1 x t') (Subst t2 x t')
  Subst ('Times t1 t2) x t' = 'Times (Subst t1 x t') (Subst t2 x t')
  Subst ('Fn t1 p t2) x t' = 'Fn (Subst t1 x t') p (Subst t2 x t')
  Subst ('Says p t) x t' = 'Says p (Subst t x t')
  Subst t _ _ = t

type family Lub (p :: Prin) (q :: Prin) :: Prin

data FLAC
  (delctx :: [Delegation])
  (typctx :: [Typed])
  (pc :: Prin) (typ :: Type) where
  EUnit :: FLAC dx tx pc 'Unit
  Var :: Lookup tx x ~ 'Just t => Proxy (x :: Symbol) -> FLAC dx tx pc t
  Del :: Proxy p -> Proxy q -> FLAC dx tx pc ('ActsFor p q)
  Lambda :: Lookup tx x ~ 'Just t =>
    Proxy (x :: Symbol) -> Proxy (t :: Type) -> Proxy (pc' :: Prin)
    -> FLAC dx tx pc' t2
    -> FLAC dx (tx :\ x) pc ('Fn t pc' t2)
  -- is this what TLam implies? X free in gamma?
  TLambda :: Member x tx ~ 'False =>
    Proxy (x :: Symbol) -> Proxy (pc' :: Prin)
    -> FLAC dx tx pc' t
    -> FLAC dx tx pc ('Forall x pc' t)
  App :: FLAC dx tx pc ('Fn t1 pc' t2)
    -> FLAC dx tx pc t1
    -> FlowsTo dx pc pc'
    -> FLAC dx tx pc t2
  -- require t' well-formed in dx
  TApp :: FLAC dx tx pc ('Forall x pc' t) -> FlowsTo dx pc pc' -> Proxy (t' :: Type)
    -> FLAC dx tx pc (Subst t x t')
  Pair :: FLAC dx tx pc t1 -> FLAC dx tx pc t2 -> FLAC dx tx pc ('Times t1 t2)
  Project1 :: FLAC dx tx pc ('Times t1 t2) -> FLAC dx tx pc t1
  Project2 :: FLAC dx tx pc ('Times t1 t2) -> FLAC dx tx pc t2
  Inject1 :: FLAC dx tx pc t1 -> FLAC dx tx pc ('Plus t1 t2)
  Inject2 :: FLAC dx tx pc t2 -> FLAC dx tx pc ('Plus t1 t2)
  Case :: (tx1 ~ ((x ':-> t1) ': tx), tx2 ~ ((y ':-> t2) ': tx)) =>
    FLAC dx tx pc ('Plus t1 t2) -> FlowsToType dx pc t
    -> Proxy (x :: Symbol) -> FLAC dx tx1 pc t
    -> Proxy (y :: Symbol) -> FLAC dx tx2 pc t
    -> FLAC dx tx pc t
  UnitM :: Proxy (l :: Prin) -> FLAC dx tx pc t -> FlowsTo dx pc l
    -> FLAC dx tx pc ('Says l t)
  -- do we end up needing this?
  -- SEALED :: FLAC dx tx pc ('Var v) t -> FLAC dx tx pc ('Protect l ('Var v)) ('Says l t)
  Bind :: tx' ~ ((x ':-> t') ': tx) =>
    Proxy (x :: Symbol) -> FLAC dx tx pc ('Says l t') -> FLAC dx tx' (Lub pc l) t
    -> FlowsToType dx (Lub pc l) t -> FLAC dx tx pc t
  Assume :: dx' ~ ('Delegation p q ': dx) => -- is this what goes into dx?
    FLAC dx tx pc ('ActsFor p q)
    -> ActsFor dx pc ('Voice q)
    -> ActsFor dx ('Voice ('Conf p)) ('Voice ('Conf q))
    -> FLAC dx' tx pc t
    -> FLAC dx tx pc t
