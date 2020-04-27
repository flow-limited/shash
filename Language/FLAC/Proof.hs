{-# LANGUAGE GADTs, EmptyDataDecls, DataKinds, FlexibleContexts, KindSignatures #-}

module Language.FLAC.Proof where

import Data.HList.HList

data Top
data Bottom
data I a = I a
data C a = C a
data And a b = And a b
data Or a b = Or a b
data Voice a = Voice a

data Delegation p q = Delegation p q

data ActsFor (ctx :: [*]) a b where
  ForBot :: a -> ActsFor ctx a Bottom
  TopFor :: a -> ActsFor ctx Top a
  Refl :: a -> ActsFor ctx a a
  IProj :: ActsFor ctx a b -> ActsFor ctx (I a) (I b)
  CProj :: ActsFor ctx a b -> ActsFor ctx (C a) (C b)
  IProjR :: a -> ActsFor ctx a (I a)
  CProjR :: a -> ActsFor ctx a (C a)
  ConjL1 :: ActsFor ctx a p -> ActsFor ctx (And a b) p
  ConjL2 :: ActsFor ctx b p -> ActsFor ctx (And a b) p
  ConjR :: ActsFor ctx p a -> ActsFor ctx p b -> ActsFor ctx p (And a b)
  DisjL :: ActsFor ctx a p -> ActsFor ctx b p -> ActsFor ctx (Or a b) p
  DisjR1 :: ActsFor ctx p a -> ActsFor ctx p (Or a b)
  DisjR2 :: ActsFor ctx p b -> ActsFor ctx p (Or a b)
  Trans :: ActsFor ctx a b -> ActsFor ctx b c -> ActsFor ctx a c
--  TransVoice :: ActsFor ctx a b -> ActsFor ctx b c -> ActsFor ctx pc (Voice (C c)) -> ActsFor ctx a c
  Assume :: HMember (Delegation p q) ctx 'True => ActsFor ctx (Voice (C p)) (Voice (C q)) -> ActsFor ctx p q
