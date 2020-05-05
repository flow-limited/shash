{-# LANGUAGE GADTs, DataKinds, FlexibleContexts, RankNTypes, TypeInType, TypeOperators, TypeFamilies #-}

module Language.FLAC.Proof where

import Language.FLAC.Syntax
import Language.FLAC.Proof.ActsFor

import Data.Type.Map hiding (Var)
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

data FLAC
  (delctx :: [Delegation])
  (typctx :: [Typed])
  (pc :: Prin) (exp :: Exp) (typ :: Type) where
  UNIT :: FLAC dx tx pc 'EUnit 'Unit
  VAR :: Lookup tx x ~ 'Just t => FLAC dx tx pc ('Var x) t
  DEL :: FLAC dx tx pc ('EActsFor p q) ('ActsFor p q)
  LAM :: Lookup tx x ~ 'Just t => FLAC dx tx pc' exp t2
    -> FLAC dx (tx :\ x) pc ('Lambda x t pc' exp) ('Fn t pc' t2)
  -- is this what TLam implies? X free in gamma?
  TLAM :: Member x tx ~ 'False => FLAC dx tx pc' e t
    -> FLAC dx tx pc ('LAMBDA x pc' e) ('Forall x pc' t)
  APP :: FLAC dx tx pc fn ('Fn t1 pc' t2) -> FLAC dx tx pc v t1 -> FlowsTo dx pc pc'
    -> FLAC dx tx pc ('App fn v) t2
  -- require t' well-formed in dx
  TAPP :: FLAC dx tx pc e ('Forall x pc' t) -> FlowsTo dx pc pc'
    -> FLAC dx tx pc ('TApp e t') (Subst t x t')
  PAIR :: FLAC dx tx pc e1 t1 -> FLAC dx tx pc e2 t2 -> FLAC dx tx pc ('Pair e1 e2) ('Times t1 t2)
  UNPAIR1 :: FLAC dx tx pc e ('Times t1 t2) -> FLAC dx tx pc ('Project1 e) t1
  UNPAIR2 :: FLAC dx tx pc e ('Times t1 t2) -> FLAC dx tx pc ('Project2 e) t2
  INJ1 :: FLAC dx tx pc e t1 -> FLAC dx tx pc ('Inject1 e) ('Plus t1 t2)
  INJ2 :: FLAC dx tx pc e t2 -> FLAC dx tx pc ('Inject2 e) ('Plus t1 t2)
  -- wait what? pc flows to a type?
  -- CASE :: FLAC dx tx pc e ('Plus t1 t2) -> FlowsTo pc t
  UNITM :: FLAC dx tx pc e t -> FlowsTo dx pc l -> FLAC dx tx pc ('Protect l e) ('Says l t)
  -- do we end up needing this?
  SEALED :: FLAC dx tx pc ('Var v) t -> FLAC dx tx pc ('Protect l ('Var v)) ('Says l t)
  -- also needs flowsto type clarification
  -- BINDM :: FLAC dx tx pc e ('Says l t') ->
  ASSUME :: dx' ~ ('Delegation p q ': dx) => -- is this what goes into dx?
    FLAC dx tx pc e ('ActsFor p q)
    -> ActsFor dx pc ('Voice q)
    -> ActsFor dx ('Voice ('Conf p)) ('Voice ('Conf q))
    -> FLAC dx' tx pc e' t
    -> FLAC dx tx pc ('Assume e e') t
