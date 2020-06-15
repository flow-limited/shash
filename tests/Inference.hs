{-# LANGUAGE OverloadedStrings #-}

import Data.Singletons.Prelude
import Data.Text (Text)
import Data.Maybe (isJust, isNothing)
import Test.Tasty
import Test.Tasty.HUnit

import Language.FLAC.Syntax.Runtime
import Language.FLAC.Proof (SFLAC(..))
import Language.FLAC.Proof.Solver.Inference

compiles :: Exp -> Assertion
compiles e = assertBool ("fails to compile " ++ show e) . isJust $ compile e

txIs :: [(Text, Type)] -> Exp -> Assertion
txIs tx e = case compile e of
  Just (SFLAC _ stx _ _ _) -> assertEqual ("tx when compiling " ++ show e) tx (fromSing stx)
  Nothing -> assertFailure ("fails to compile" ++ show e)

dxIs :: [(Prin, Prin)] -> Exp -> Assertion
dxIs dx e = case compile e of
  Just (SFLAC sdx _ _ _ _) -> assertEqual ("dx when compiling " ++ show e) dx (fromSing sdx)
  Nothing -> assertFailure ("fails to compile" ++ show e)

fails :: Exp -> Assertion
fails e = assertBool ("incorrectly compiles " ++ show e) . isNothing $ compile e


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [compileTests]

compileTests :: TestTree
compileTests = testGroup "toType" [eunits, vars, pairs, cases, lam, app]

eunits :: TestTree
eunits = testGroup "EUnit"
  [
    testCase "compiles" $ compiles EUnit
  ]

vars :: TestTree
vars = testGroup "Var"
  [
    testCase "var inferred with fresh variable" $ txIs [("x", TVar "__f1")] (Var "x")
  ]

pairs :: TestTree
pairs = testGroup "Pair"
  [
    testCase "unit,unit" $ compiles (Pair EUnit EUnit),
    testCase "x,y" $ txIs [("x", TVar "__f1"), ("y", TVar "__f2")] (Pair (Var "x") (Var "y"))
  ]

cases :: TestTree
cases = testGroup "Case"
  [
    testCase "needs matching types" $ txIs [("a", Unit)] (Case (Inject1 (Var "a") Nothing)
                                                          "x" (Pair (Var "x") EUnit)
                                                          "y" (Pair EUnit (Var "y"))),
    testCase "fails if subcase doesn't prove" $ fails (Case (Inject1 (Var "a") (Just Unit))
                                                       "x" (Var "x")
                                                       "y" (Var "y"))
  ]

lam :: TestTree
lam = testGroup "Lam"
  [
    testCase "using var" $ compiles (Lam "x" Unit (Raw "alice") (Var "x")),
    testCase "unused var" $ compiles (Lam "x" Unit (Raw "alice") EUnit)
  ]

app :: TestTree
app = testGroup "App"
  [
    testCase "matching pc" $ dxIs [] (App (l Top) EUnit),
    testCase "unmatching pc" $ dxIs [(Conf alice, Conf Top), (Integ Top, Integ alice)]
      (App (l alice) EUnit)
  ]
  where l pc = Lam "x" Unit pc (Var "x")
        alice = Raw "alice"
