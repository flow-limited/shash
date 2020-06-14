{-# LANGUAGE DataKinds, TypeOperators, TypeApplications #-}

module Main where

import Language.FLAC.Syntax.Promoted
import Language.FLAC.Proof
import Data.Singletons

unit :: FLAC '[] '[] 'Bot 'Unit
unit = EUnit

var :: FLAC '[] '[ '("x", 'TVar "a") ] 'Bot ('TVar "a")
var = Var (sing @"x")

del :: FLAC '[] '[] 'Bot ('ActsFor ('Raw "p") ('Raw "q"))
del = Del sing sing

lam :: FLAC '[] '[] 'Top ('Fn ('TVar "a") 'Top 'Unit)
lam = Lambda (sing @"x") sing sing (EUnit @'[] @'[ '("x", 'TVar "a") ])

pair :: FLAC '[] '[ '("x", 'Says 'Top 'Unit), '("y", 'Unit) ] 'Bot ('Times ('Says 'Top 'Unit) 'Unit)
pair = Pair (Var $ sing @"x") (Var $ sing @"y")

inj :: FLAC '[] '[] 'Bot ('Plus ('Says 'Top 'Unit) 'Unit)
inj = Inject2 EUnit

case_ :: FLAC '[] '[] 'Bot 'Unit
case_ = Case (Inject1 EUnit) (sing @"x") EUnit (sing @"y") EUnit

main :: IO ()
main = return ()
