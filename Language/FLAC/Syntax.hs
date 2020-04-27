{-# LANGUAGE UnicodeSyntax #-}

module Language.FLAC.Syntax where

data Prin = Name String | PVar String | Top | Bot
  | Integ Prin | Conf Prin
  | Conj Prin Prin | Disj Prin Prin
  | Voice Prin | Eye Prin
  deriving (Show, Eq)

data Type = ActsFor Prin Prin | Unit | Plus Type Type | Times Type Type
  | Fn Type Prin Type | Says Prin Type
  | TVar String | Forall String Prin Type

data Exp = EUnit | Var String | EActsFor Prin Prin | App Exp Exp | Pair Exp Exp
  | Protect Prin Exp | TApp Exp Type | Project Int Exp | Inject Int Exp
  | Case Exp String Exp String Exp | Bind String Exp Exp | Assume Exp Exp
  | Lambda String Type Prin Exp
  | LAMBDA String Prin Exp

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
