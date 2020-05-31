module Language.FLAC.Syntax.Runtime where

import Data.Text (Text)

data Prin = Raw Text | PVar Text | Top | Bot
          | Integ Prin | Conf Prin
          | Conj Prin Prin | Disj Prin Prin
          | Voice Prin | Eye Prin
          deriving (Show, Eq)

data Type = ActsFor Prin Prin | Unit | Plus Type Type | Times Type Type
          | Fn Type Prin Type | Says Prin Type
          | TVar Text | Forall Text Prin Type
          deriving (Show, Eq)

data Exp = EUnit | Var Text | EActsFor Prin Prin | App Exp Exp | Pair Exp Exp
         | Protect Prin Exp | TApp Exp Type | Project1 Exp | Project2 Exp | Inject1 Exp | Inject2 Exp
         | Case Exp Text Exp Text Exp | Bind Text Exp Exp | Assume Exp Exp
         | Lam Text Type Prin Exp
         | LAM Text Prin Exp
         deriving (Show, Eq)
