{-# LANGUAGE OverloadedStrings #-}

import Data.Singletons.Prelude
import Data.Text (Text)
import Data.Maybe (isJust, isNothing)
import Test.Tasty
import Test.Tasty.HUnit

import Language.FLAC.Syntax.Runtime
import Language.FLAC.Proof (SFLAC(..))
import Language.FLAC.Proof.Solver.Inference

compiles :: Prin -> Exp -> Assertion
compiles pc e = assertBool ("fails to compile " ++ show e) . isJust $ compile pc e

txIs :: [(Text, Type)] -> Prin -> Exp -> Assertion
txIs tx pc e = case compile pc e of
  Just (SFLAC _ stx _ _ _) -> assertEqual ("tx when compiling " ++ show e) tx (fromSing stx)
  Nothing -> assertFailure ("fails to compile" ++ show e)

dxIs :: [(Prin, Prin)] -> Prin -> Exp -> Assertion
dxIs dx pc e = dxUnderGivensIs [] dx pc e

dxUnderGivensIs :: [(Prin, Prin)] -> [(Prin, Prin)] -> Prin -> Exp -> Assertion
dxUnderGivensIs givens dx pc e = case compileWithGivens pc givens e of
  Just (SFLAC sdx _ _ _ _) -> assertEqual ("dx when compiling " ++ show e) dx (fromSing sdx)
  Nothing -> assertFailure ("fails to compile" ++ show e)

fails :: Prin -> Exp -> Assertion
fails pc e = failsUnderGivens pc [] e

failsUnderGivens :: Prin -> [(Prin, Prin)] -> Exp -> Assertion
failsUnderGivens pc givens e =
  assertBool ("incorrectly compiles " ++ show e) . isNothing $ compileWithGivens pc givens e

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [compileTests]

compileTests :: TestTree
compileTests = testGroup "toType" [eunits, vars, pairs, cases, lam, app]

eunits :: TestTree
eunits = testGroup "EUnit"
  [
    testCase "compiles" $ compiles Top EUnit
  ]

vars :: TestTree
vars = testGroup "Var"
  [
    testCase "var inferred with fresh variable" $ txIs [("x", TVar "__f1")] Top (Var "x")
  ]

pairs :: TestTree
pairs = testGroup "Pair"
  [
    testCase "unit,unit" $ compiles Top (Pair EUnit EUnit),
    testCase "x,y" $ txIs [("x", TVar "__f1"), ("y", TVar "__f2")] Top
      (Pair (Var "x") (Var "y"))
  ]

cases :: TestTree
cases = testGroup "Case"
  [
    testCase "needs matching types" $ txIs [("a", Unit)] Top
      (Case (Inject1 (Var "a") Nothing)
       "x" (Pair (Var "x") EUnit)
       "y" (Pair EUnit (Var "y"))),
    testCase "fails if subcase doesn't prove" $ fails Top
      (Case (Inject1 (Var "a") (Just Unit))
        "x" (Var "x")
        "y" (Var "y"))
  ]

lam :: TestTree
lam = testGroup "Lam"
  [
    testCase "using var" $ compiles Top (Lam "x" Unit (Raw "alice") (Var "x")),
    testCase "unused var" $ compiles Top (Lam "x" Unit (Raw "alice") EUnit)
  ]

app :: TestTree
app = testGroup "App"
  [
    testCase "matching pc 1" $ dxIs [] Top (App (l Top) EUnit),
    testCase "matching pc 2" $ dxIs [] alice (App (l alice) EUnit),
    testCase "unmatching pc 1" $ fails Top (App (l alice) EUnit),
    testCase "unmatching pc 2" $ dxUnderGivensIs aTop aTop Top (App (l alice) EUnit),
    testCase "unmatching pc 3" $ fails Bot (App (l alice) EUnit),
    testCase "unmatching pc 4" $ dxUnderGivensIs botA botA Bot (App (l alice) EUnit)
  ]
  where l pc = Lam "x" Unit pc (Var "x")
        alice = Raw "alice"
        aTop = [(alice, Top)]
        botA = [(Bot, alice)]
