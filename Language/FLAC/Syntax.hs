{-# LANGUAGE UnicodeSyntax, DefaultSignatures, EmptyCase, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GADTs, InstanceSigs, KindSignatures, RankNTypes, ScopedTypeVariables, TemplateHaskell, TypeFamilies, TypeInType, TypeOperators, UndecidableInstances, TypeApplications, StandaloneKindSignatures, OverloadedStrings #-}

module Language.FLAC.Syntax where

import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.TH.Options
import Data.Text (Text)
import Language.Haskell.TH (Name)

data RPrin = RRaw Text | RPVar Text | RTop | RBot
          | RInteg RPrin | RConf RPrin
          | RConj RPrin RPrin | RDisj RPrin RPrin
          | RVoice RPrin | REye RPrin

data Prin = Raw Symbol | PVar Symbol | Top | Bot
          | Integ Prin | Conf Prin
          | Conj Prin Prin | Disj Prin Prin
          | Voice Prin | Eye Prin

data RType = RActsFor RPrin RPrin | RUnit | RPlus RType RType | RTimes RType RType
          | RFn RType RPrin RType | RSays RPrin RType
          | RTVar Text | RForall Text RPrin RType

data Type = ActsFor Prin Prin | Unit | Plus Type Type | Times Type Type
          | Fn Type Prin Type | Says Prin Type
          | TVar Symbol | Forall Symbol Prin Type

data Exp = EUnit | Var String | EActsFor Prin Prin | App Exp Exp | Pair Exp Exp
         | Protect Prin Exp | TApp Exp Type | Project1 Exp | Project2 Exp | Inject1 Exp | Inject2 Exp
         | Case Exp String Exp String Exp | Bind String Exp Exp | Assume Exp Exp
         | Lam String Type Prin Exp
         | LAM String Prin Exp


$(let customPromote :: Name -> Name
      customPromote n
        | n == ''RPrin       = ''Prin
        | n == 'RRaw         = 'Raw
        | n == 'RPVar        = 'PVar
        | n == 'RTop         = 'Top
        | n == 'RBot         = 'Bot
        | n == 'RInteg       = 'Integ
        | n == 'RConf        = 'Conf
        | n == 'RConj        = 'Conj
        | n == 'RDisj        = 'Disj
        | n == 'RVoice       = 'Voice
        | n == 'REye         = 'Eye
        | n == ''RType       = ''Type
        | n == 'RActsFor     = 'ActsFor
        | n == 'RUnit        = 'Unit
        | n == 'RPlus        = 'Plus
        | n == 'RTimes       = 'Times
        | n == 'RFn          = 'Fn
        | n == 'RSays        = 'Says
        | n == 'RTVar        = 'TVar
        | n == 'RForall      = 'Forall
        | n == ''Text        = ''Symbol
        | otherwise      = promotedDataTypeOrConName defaultOptions n

      customDefun :: Name -> Int -> Name
      customDefun n sat = defunctionalizedName defaultOptions (customPromote n) sat in

  withOptions defaultOptions{ promotedDataTypeOrConName = customPromote
                            , defunctionalizedName      = customDefun
                            } $ genSingletons [''RPrin, ''RType]
    )


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
