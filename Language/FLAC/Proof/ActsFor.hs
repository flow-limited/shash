{-# LANGUAGE GADTs, EmptyDataDecls, DataKinds, FlexibleContexts, KindSignatures, RankNTypes, TypeInType #-}

module Language.FLAC.Proof.ActsFor where
import Language.FLAC.Syntax

data Delegation = Delegation Prin Prin

data ActsFor (ctx :: [Delegation]) (a :: Prin) (b :: Prin) where
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

type FlowsTo (ctx :: [Delegation]) (a :: Prin) (b :: Prin) = (ActsFor ctx ('Conf b) ('Conf a), ActsFor ctx ('Integ a) ('Integ b))
