{-# LANGUAGE UnicodeSyntax #-}

module Language.FLAC.Syntax where

import GHC.TypeLits

data Prin = Name String | PVar String | Top | Bot
  | Integ Prin | Conf Prin
  | Conj Prin Prin | Disj Prin Prin
  | Voice Prin | Eye Prin
  deriving (Show, Eq)

data Type = ActsFor Prin Prin | Unit | Plus Type Type | Times Type Type
  | Fn Type Prin Type | Says Prin Type
  | TVar Symbol | Forall Symbol Prin Type

data Exp = EUnit | Var Symbol | EActsFor Prin Prin | App Exp Exp | Pair Exp Exp
  | Protect Prin Exp | TApp Exp Type | Project1 Exp | Project2 Exp | Inject1 Exp | Inject2 Exp
  | Case Exp String Exp String Exp | Bind String Exp Exp | Assume Exp Exp
  | Lambda Symbol Type Prin Exp
  | LAMBDA Symbol Prin Exp

(^→), (^←) :: Prin -> Prin
(^→) = Conf
(^←) = Integ

(∧), (∨) :: Prin -> Prin -> Prin
(∧) = Conj
(∨) = Disj

(≽) :: Prin -> Prin -> Type
(≽) = ActsFor

(+), (×) :: Type -> Type -> Type
(+) = Plus
(×) = Times

says :: Prin -> Type -> Type
says = Says
