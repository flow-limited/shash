module Language.FLAC.Syntax.Promoted where

import GHC.TypeLits (Symbol)

data Prin = Raw Symbol | PVar Symbol | Top | Bot
          | Integ Prin | Conf Prin
          | Conj Prin Prin | Disj Prin Prin
          | Voice Prin | Eye Prin

data Type = ActsFor Prin Prin | Unit | Plus Type Type | Times Type Type
          | Fn Type Prin Type | Says Prin Type
          | TVar Symbol | Forall Symbol Prin Type
