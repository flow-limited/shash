{-# LANGUAGE GADTs, EmptyDataDecls, DataKinds, FlexibleContexts, KindSignatures, RankNTypes, TypeInType, TypeOperators, TypeFamilies, StandaloneDeriving #-}

module Language.FLAC.Proof.ActsFor where

import GHC.TypeLits
import Language.FLAC.Syntax.Promoted

type Typed = (Symbol, Type)
type Delegation = (Prin, Prin)

data ActsFor (ctx :: [Delegation]) (a :: Prin) (b :: Prin) where
  FAKE :: ActsFor ctx a b
  ForBot :: forall ctx a. ActsFor ctx a 'Bot
  TopFor :: forall ctx a. ActsFor ctx 'Top a
  Refl :: forall ctx a. ActsFor ctx a a
  IProj :: ActsFor ctx a b -> ActsFor ctx ('Integ a) ('Integ b)
  CProj :: ActsFor ctx a b -> ActsFor ctx ('Conf a) ('Conf b)
  IProjR :: forall ctx a. ActsFor ctx a ('Integ a)
  CProjR :: forall ctx a. ActsFor ctx a ('Conf a)
  ConjL1 :: ActsFor ctx a p -> ActsFor ctx ('Conj a b) p
  ConjL2 :: ActsFor ctx b p -> ActsFor ctx ('Conj a b) p
  ConjR :: ActsFor ctx p a -> ActsFor ctx p b -> ActsFor ctx p ('Conj a b)
  DisjL :: ActsFor ctx a p -> ActsFor ctx b p -> ActsFor ctx ('Disj a b) p
  DisjR1 :: ActsFor ctx p a -> ActsFor ctx p ('Disj a b)
  DisjR2 :: ActsFor ctx p b -> ActsFor ctx p ('Disj a b)
  Trans :: ActsFor ctx a b -> ActsFor ctx b c -> ActsFor ctx a c
--  Assume :: HMember (Delegation p q) ctx 'True => ActsFor ctx ('Voice ('Conf p)) ('Voice ('Conf q)) -> ActsFor ctx p q

deriving instance Show (ActsFor dx a b)

type FlowsTo (ctx :: [Delegation]) (a :: Prin) (b :: Prin) = (ActsFor ctx ('Conf b) ('Conf a), ActsFor ctx ('Integ a) ('Integ b))

data FlowsToType (ctx :: [Delegation]) (a :: Prin) (t :: Type) where
  FAKET :: FlowsToType dx l t
  PUNIT :: FlowsToType dx l 'Unit
  PPAIR :: FlowsToType dx l a -> FlowsToType dx l b -> FlowsToType dx l ('Times a b)
  PFUN :: FlowsToType dx l t2 -> FlowsTo dx l pc' -> FlowsToType dx l ('Fn t1 pc' t2)
  PTFUN :: FlowsToType dx l t -> FlowsTo dx l pc' -> FlowsToType dx l ('Forall x pc' t)
  PLBL :: FlowsTo dx l l' -> FlowsToType dx l ('Says l t)

deriving instance Show (FlowsToType dx a t)
