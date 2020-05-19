{-# LANGUAGE DataKinds, TypeOperators, TypeApplications #-}

module Main where

import Language.FLAC.Syntax
import Language.FLAC.Proof
import Language.FLAC.Proof.ActsFor
import Data.Type.Map hiding (Var)

unit :: FLAC '[] '[] 'Bot 'EUnit 'Unit
unit = UNIT

var :: FLAC '[] '["x" ':-> 'TVar "a"] 'Bot ('Var "x") ('TVar "a")
var = VAR

lam :: FLAC '[] '[] 'Top ('Lambda "x" ('TVar "a") 'Top 'EUnit) ('Fn ('TVar "a") 'Top 'Unit)
lam = LAM (UNIT @'[] @'["x" ':-> 'TVar "a"])

pair :: FLAC '[] '["x" ':-> 'Says 'Top 'Unit, "y" ':-> 'Unit] 'Bot ('Pair ('Var "x") ('Var "y")) ('Times ('Says 'Top 'Unit) 'Unit)
pair = PAIR VAR VAR

inj :: FLAC '[] '[] 'Bot ('Inject2 'EUnit) ('Plus ('Says 'Top 'Unit) 'Unit)
inj = INJ2 UNIT

case_ :: FLAC '[] '[] 'Bot ('Case ('Inject1 'EUnit) "k" 'EUnit "z" 'EUnit) 'Unit
case_ = CASE (INJ1 UNIT) PUNIT UNIT UNIT

main :: IO ()
main = return ()
