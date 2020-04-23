{-# LANGUAGE UnicodeSyntax #-}

module Language.FLAC.Syntax where

data Principal = Primitive String | Top | Bottom
  | Integrity Principal | Confidentiality Principal
  | And Principal Principal | Or Principal Principal
  deriving (Show, Eq)

data Type = ActsFor Principal Principal | Unit | Plus Type Type | Times Type Type
  | Fn Type Principal Type | Says Principal Type
  | TVar String | Forall String Principal Type

data Value = VUnit | VPair Value Value | VActsFor Principal Principal
  | VProtect Principal Value | VInject Int Value
  | Lambda String Type Principal Exp
  | LAMBDA String Principal Exp

data Exp = Var String | Val Value | App Exp Exp | Pair Exp Exp
  | Protect Principal Exp | TApp Exp Type | Project Int Exp | Inject Int Exp
  | Case Exp String Exp String Exp | Bind String Exp Exp | Assume Exp Exp

(^→), (^←) :: Principal -> Principal
(^→) = Confidentiality
(^←) = Integrity

(∧), (∨) :: Principal -> Principal -> Principal
(∧) = And
(∨) = Or

(≽) :: Principal -> Principal -> Type
(≽) = ActsFor

(+), (×) :: Type -> Type -> Type
(+) = Plus
(×) = Times

says :: Principal -> Type -> Type
says = Says
