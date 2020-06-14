{-# LANGUAGE OverloadedStrings #-}

import Data.Text (Text)
import Data.Maybe (isJust, isNothing)
import Test.Tasty
import Test.Tasty.HUnit

import Language.FLAC.Syntax.Runtime
import Language.FLAC.Proof.TypeCheck

showps :: Exp -> DelCtx -> TyCtx -> Prin -> String
showps e dx tx pc = show dx ++ " " ++ show tx ++ " " ++ show pc ++ " ⊢ " ++ show e

proves :: Exp -> DelCtx -> TyCtx -> Prin -> Assertion
proves e dx tx pc = assertBool ("fails to prove " ++ showps e dx tx pc) . isJust $
  prove e dx tx pc

fails :: Exp -> DelCtx -> TyCtx -> Prin -> Assertion
fails e dx tx pc = assertBool ("incorrectly proves " ++ showps e dx tx pc) . isNothing $
  prove e dx tx pc



main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [toTypeTests]

toTypeTests :: TestTree
toTypeTests = testGroup "toType" [ eunits, vars, pairs, cases, lam, app]

eunits :: TestTree
eunits = testGroup "EUnit"
  [
    testCase "empty ctxs" $ proves EUnit [] [] Bot,
    testCase "has ctxs" $ proves EUnit [(Raw "p", Raw "q")] [("x", Unit)] Top
  ]

vars :: TestTree
vars = testGroup "Var"
  [
    testCase "empty ctxs" $ fails (Var "x") [] [] Bot,
    testCase "relevant ctxs" $ proves (Var "y") [(Raw "p", Raw "q")] [("y", Unit)] Top,
    testCase "irrelevant ctxs" $ fails (Var "x") [(Raw "p", Raw "q")] [("y", Unit)] Top
  ]

pairs :: TestTree
pairs = testGroup "Pair"
  [
    testCase "unit,unit" $ proves (Pair EUnit EUnit) [] [] Bot,
    testCase "x,y" $ proves (Pair (Var "x") (Var "y")) [] [("x", Unit), ("y", Unit)] Top,
    testCase "x,y, x missing" $ fails (Pair (Var "x") (Var "y")) [] [("y", Unit)] Top,
    testCase "x,y, y missing" $ fails (Pair (Var "x") (Var "y")) [] [("x", Unit)] Top,
    testCase "x,y, both missing" $ fails (Pair (Var "x") (Var "y")) [] [] Top
  ]

cases :: TestTree
cases = testGroup "Case"
  [
    testCase "needs matching types" $ proves (Case (Inject1 (Var "a") (Just Unit))
                                              "x" (Pair (Var "x") EUnit)
                                              "y" (Pair EUnit (Var "y")))
    [] [("a", Unit)] Top,
    testCase "fails if subcase doesn't prove" $ fails (Case (Inject1 (Var "a") (Just Unit))
                                                       "x" (Var "x")
                                                       "y" (Var "y")) [] [] Top
  ]

lam :: TestTree
lam = testGroup "Lam"
  [
    testCase "using var" $ proves (Lam "x" Unit (Raw "alice") (Var "x")) [] [] Top,
    testCase "unused var" $ proves (Lam "x" Unit (Raw "alice") EUnit) [] [] Top
  ]

app :: TestTree
app = testGroup "App"
  [
    testCase "matching pc 1" $ proves (App (l Top) EUnit) [] [] Top,
    testCase "matching pc 2" $ proves (App (l alice) EUnit) [] [] alice,
    testCase "unmatching pc 1" $ fails (App (l alice) EUnit) [] [] Top,
    testCase "unmatching pc 2" $ proves (App (l alice) EUnit) [(alice, Top)] [] Top
  ]
  where l pc = Lam "x" Unit pc (Var "x")
        alice = Raw "alice"
