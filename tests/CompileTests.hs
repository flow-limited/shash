{-# LANGUAGE DataKinds, TypeOperators, TypeApplications #-}

module Main where

import Language.FLAC.Syntax hiding (Exp(..))
import Language.FLAC.Proof
import Language.FLAC.Proof.ActsFor
import Data.Proxy
import Data.Type.Map hiding (Var)

unit :: FLAC '[] '[] 'Bot 'Unit
unit = EUnit

var :: FLAC '[] '["x" ':-> 'TVar "a"] 'Bot ('TVar "a")
var = Var (Proxy @"x")

lam :: FLAC '[] '[] 'Top ('Fn ('TVar "a") 'Top 'Unit)
lam = Lambda (Proxy @"x") Proxy Proxy (EUnit @'[] @'["x" ':-> 'TVar "a"])

pair :: FLAC '[] '["x" ':-> 'Says 'Top 'Unit, "y" ':-> 'Unit] 'Bot ('Times ('Says 'Top 'Unit) 'Unit)
pair = Pair (Var $ Proxy @"x") (Var $ Proxy @"y")

inj :: FLAC '[] '[] 'Bot ('Plus ('Says 'Top 'Unit) 'Unit)
inj = Inject2 EUnit

case_ :: FLAC '[] '[] 'Bot 'Unit
case_ = Case (Inject1 EUnit) PUNIT Proxy EUnit Proxy EUnit

main :: IO ()
main = return ()
