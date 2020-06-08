{-# LANGUAGE UnicodeSyntax, DefaultSignatures, EmptyCase, ExistentialQuantification, FlexibleContexts, FlexibleInstances, GADTs, InstanceSigs, KindSignatures, RankNTypes, ScopedTypeVariables, TemplateHaskell, TypeFamilies, TypeInType, TypeOperators, UndecidableInstances, TypeApplications, StandaloneKindSignatures, OverloadedStrings, StandaloneDeriving #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.FLAC.Syntax where

import Data.Singletons.TH
import Data.Singletons.TH.Options
import Data.Singletons.Prelude.Bool

import Language.FLAC.Syntax.Runtime as R
import Language.FLAC.Syntax.Promoted as P

import Language.FLAC.Syntax.TH (promotionOptions)

$(withOptions promotionOptions $ do
     ss <- genSingletons [''R.Prin, ''R.Type]
     di <- singDecideInstances [''P.Prin, ''P.Type]
     ei <- singEqInstances [''P.Prin]
     return $ ss ++ di ++ ei)
deriving instance Show P.Prin
deriving instance Show P.Type
deriving instance Show (SPrin a)
deriving instance Show (SType a)
deriving instance Eq (P.Prin)

(^→), (^←) :: P.Prin -> P.Prin
(^→) = P.Conf
(^←) = P.Integ

(∧), (∨) :: P.Prin -> P.Prin -> P.Prin
(∧) = P.Conj
(∨) = P.Disj

(≽) :: P.Prin -> P.Prin -> P.Type
(≽) = P.ActsFor

(+), (×) :: P.Type -> P.Type -> P.Type
(+) = P.Plus
(×) = P.Times

says :: P.Prin -> P.Type -> P.Type
says = P.Says
