{-# LANGUAGE GADTs, DataKinds, TypeOperators, TypeFamilies, TypeApplications, ScopedTypeVariables, PolyKinds, StandaloneKindSignatures, UndecidableInstances, TemplateHaskell, StandaloneDeriving #-}

module Language.FLAC.Proof where

import Language.FLAC.Syntax
import Language.FLAC.Syntax.TH
import Language.FLAC.Syntax.Promoted
import Language.FLAC.Proof.ActsFor

import Control.Monad.Trans.Class (lift)
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.TH.Options
import Data.Singletons.Prelude.List
import GHC.TypeLits

$(withOptions promotionOptions $ singletons $ lift [d|
  remove :: Eq a => a -> [(a,b)] -> [(a,b)]
  remove _ [] = []
  remove a ((b,d):bs) = if (a == b) then remove a bs else (b,d):(remove a bs)

  subst :: Type -> Symbol -> Type -> Type
  subst v@(TVar x) y t = if (x == y) then t else v
  subst (Forall x p t) y t' = if (x == y) then Forall x p t else Forall x p (subst t y t')
  subst (Plus t1 t2) x t = Plus (subst t1 x t) (subst t2 x t)
  subst (Times t1 t2) x t = Times (subst t1 x t) (subst t2 x t)
  subst (Fn t1 p t2) x t' = Fn (subst t1 x t') p (subst t2 x t')
  subst (Says p t) x t' = Says p (subst t x t')
  subst (ActsFor p q) _ _ = ActsFor p q
  subst Unit _ _ = Unit

  lub :: Prin -> Prin -> Prin
  lub p q = Conj (Conf (Conj p q)) (Integ (Disj p q))
                                                     |])

data FLAC
  (delctx :: [Delegation])
  (typctx :: [Typed])
  (pc :: Prin) (typ :: Type) where
  EUnit :: FLAC dx tx pc 'Unit
  Var :: Lookup x tx ~ 'Just t => Sing (x :: Symbol) -> FLAC dx tx pc t
  Del :: Sing p -> Sing q -> FLAC dx tx pc ('ActsFor p q)
  Lambda :: Lookup x tx ~ 'Just t =>
    Sing (x :: Symbol) -> Sing (t :: Type) -> Sing (pc' :: Prin)
    -> FLAC dx tx pc' t2
    -> FLAC dx (Remove x tx) pc ('Fn t pc' t2)
  -- is this what TLam implies? X free in gamma?
  TLambda :: Lookup x tx ~ 'Nothing =>
    Sing (x :: Symbol) -> Sing (pc' :: Prin)
    -> FLAC dx tx pc' t
    -> FLAC dx tx pc ('Forall x pc' t)
  App :: FLAC dx tx pc ('Fn t1 pc' t2)
    -> FLAC dx tx pc t1
    -> FlowsTo dx pc pc'
    -> FLAC dx tx pc t2
  -- require t' well-formed in dx
  TApp :: FLAC dx tx pc ('Forall x pc' t) -> FlowsTo dx pc pc' -> Sing (t' :: Type)
    -> FLAC dx tx pc (Subst t x t')
  Pair :: FLAC dx tx pc t1 -> FLAC dx tx pc t2 -> FLAC dx tx pc ('Times t1 t2)
  Project1 :: FLAC dx tx pc ('Times t1 t2) -> FLAC dx tx pc t1
  Project2 :: FLAC dx tx pc ('Times t1 t2) -> FLAC dx tx pc t2
  Inject1 :: FLAC dx tx pc t1 -> FLAC dx tx pc ('Plus t1 t2)
  Inject2 :: FLAC dx tx pc t2 -> FLAC dx tx pc ('Plus t1 t2)
  Case :: (tx1 ~ ('(x, t1) ': tx), tx2 ~ ('(y, t2) ': tx)) =>
    FLAC dx tx pc ('Plus t1 t2) -> FlowsToType dx pc t
    -> Sing (x :: Symbol) -> FLAC dx tx1 pc t
    -> Sing (y :: Symbol) -> FLAC dx tx2 pc t
    -> FLAC dx tx pc t
  UnitM :: Sing (l :: Prin) -> FLAC dx tx pc t -> FlowsTo dx pc l
    -> FLAC dx tx pc ('Says l t)
  -- do we end up needing this?
  -- SEALED :: FLAC dx tx pc ('Var v) t -> FLAC dx tx pc ('Protect l ('Var v)) ('Says l t)
  Bind :: tx' ~ ('(x, t') ': tx) =>
    Sing (x :: Symbol) -> FLAC dx tx pc ('Says l t') -> FLAC dx tx' (Lub pc l) t
    -> FlowsToType dx (Lub pc l) t -> FLAC dx tx pc t
  Assume :: dx' ~ ('(p, q) ': dx) => -- is this what goes into dx?
    FLAC dx tx pc ('ActsFor p q)
    -> ActsFor dx pc ('Voice q)
    -> ActsFor dx ('Voice ('Conf p)) ('Voice ('Conf q))
    -> FLAC dx' tx pc t
    -> FLAC dx tx pc t

deriving instance Show (FLAC dx tx pc t)

data SFLAC where
  SFLAC :: Sing (dx :: [Delegation])
        -> Sing (tx :: [Typed])
        -> Sing (p :: Prin)
        -> Sing (t :: Type) -> FLAC dx tx p t -> SFLAC

deriving instance Show SFLAC
