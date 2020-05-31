{-# LANGUAGE UnicodeSyntax, DefaultSignatures, EmptyCase, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GADTs, InstanceSigs, KindSignatures, RankNTypes, ScopedTypeVariables, TemplateHaskell, TypeFamilies, TypeInType, TypeOperators, UndecidableInstances, TypeApplications, StandaloneKindSignatures, OverloadedStrings #-}

module Language.FLAC.Syntax.TH where

import GHC.TypeLits (Symbol)
import Data.Singletons.TH.Options
import Data.Text (Text)

import Language.FLAC.Syntax.Runtime as R
import Language.FLAC.Syntax.Promoted as P
import Language.Haskell.TH (Name)

promotionOptions :: Options
promotionOptions = defaultOptions {
  promotedDataTypeOrConName = customPromote,
  defunctionalizedName      = customDefun
  }
  where customPromote :: Name -> Name
        customPromote n
          | n == ''R.Prin       = ''P.Prin
          | n == 'R.Raw         = 'P.Raw
          | n == 'R.PVar        = 'P.PVar
          | n == 'R.Top         = 'P.Top
          | n == 'R.Bot         = 'P.Bot
          | n == 'R.Integ       = 'P.Integ
          | n == 'R.Conf        = 'P.Conf
          | n == 'R.Conj        = 'P.Conj
          | n == 'R.Disj        = 'P.Disj
          | n == 'R.Voice       = 'P.Voice
          | n == 'R.Eye         = 'P.Eye
          | n == ''R.Type       = ''P.Type
          | n == 'R.ActsFor     = 'P.ActsFor
          | n == 'R.Unit        = 'P.Unit
          | n == 'R.Plus        = 'P.Plus
          | n == 'R.Times       = 'P.Times
          | n == 'R.Fn          = 'P.Fn
          | n == 'R.Says        = 'P.Says
          | n == 'R.TVar        = 'P.TVar
          | n == 'R.Forall      = 'P.Forall
          | n == ''Text        = ''Symbol
          | otherwise      = promotedDataTypeOrConName defaultOptions n
        customDefun :: Name -> Int -> Name
        customDefun n sat = defunctionalizedName defaultOptions (customPromote n) sat
