{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverloadedStrings #-}
module Language.FLAC.Proof.Solver.Inference where

import Prelude hiding (take, exp)
import Data.List (delete)

import Language.FLAC.Syntax.Runtime
import Language.FLAC.Proof (SFLAC, rSubst, rLub)
import Language.FLAC.Proof.Solver.Delegations (inferDelegations)
import qualified Language.FLAC.Proof.TypeCheck as TC

import qualified Data.Map as M
import Data.Text (Text, pack, take)
import Control.Monad.State
import Control.Monad.Trans.Maybe

type Dx = [(Prin, Prin)]
type Tx = M.Map Text Type
type TyC = [(Type, Type)]
newtype FreshVar = FreshVar Int

data InferCtx = InferCtx { dx :: Dx, tx :: Tx, tyc :: TyC, exp :: Exp, ty :: Type }
  deriving Show

type Infer a = MaybeT (State FreshVar) a
type InferState = Infer InferCtx

class Subst a where
  substTVar :: Text -> Type -> a -> a
  substPVar :: Text -> Prin -> a -> a

substPrin :: Subst a => Prin -> Prin -> a -> Maybe a
substPrin (PVar x) (PVar y) a | isFresh x = Just $ substPVar x (PVar y) a
substPrin (PVar x) (PVar y) a | isFresh y = Just $ substPVar y (PVar x) a
substPrin (PVar x) p a = Just $ substPVar x p a
substPrin p (PVar x) a = Just $ substPVar x p a
substPrin (Raw n) (Raw n') a | n == n' = Just a
substPrin Top Top a = Just a
substPrin Bot Bot a = Just a
substPrin (Integ p) (Integ p') a = substPrin p p' a
substPrin (Conf p) (Conf p') a = substPrin p p' a
substPrin (Conj p q) (Conj p' q') a = substPrin p p' a >>= substPrin q q'
substPrin (Disj p q) (Disj p' q') a = substPrin p p' a >>= substPrin q q'
substPrin (Voice p) (Voice p') a = substPrin p p' a
substPrin (Eye p) (Eye p') a = substPrin p p' a
substPrin _ _ _ = Nothing

subst :: Subst a => Type -> Type -> a -> Maybe a
subst (TVar x) (TVar y) a | isFresh x = Just $ substTVar x (TVar y) a
subst (TVar x) (TVar y) a | isFresh y = Just $ substTVar y (TVar x) a
subst (TVar x) t a = Just $ substTVar x t a
subst t (TVar x) a = Just $ substTVar x t a
subst Unit Unit a = Just a
subst (Plus s t) (Plus s' t') a = subst s s' a >>= subst t t'
subst (Times s t) (Times s' t') a = subst s s' a >>= subst t t'
subst (ActsFor p q) (ActsFor p' q') a = substPrin p p' a >>= substPrin q q'
subst (Fn s p t) (Fn s' p' t') a = subst s s' a >>= substPrin p p' >>= subst t t'
subst (Says p t) (Says p' t') a = substPrin p p' a >>= subst t t'
subst (Forall x p t) (Forall x' p' t') a | x == x' = substPrin p p' a >>= subst t t'
subst _ _ _ = Nothing

instance Subst Prin where
  substPVar x p (PVar y) | x == y = p
  substPVar x p (Integ q) = Integ (substPVar x p q)
  substPVar x p (Conf q) = Conf (substPVar x p q)
  substPVar x p (Conj q r) = Conj (substPVar x p q) (substPVar x p r)
  substPVar x p (Disj q r) = Disj (substPVar x p q) (substPVar x p r)
  substPVar x p (Voice q) = Voice (substPVar x p q)
  substPVar x p (Eye q) = Eye (substPVar x p q)
  substPVar _ _ a = a
  substTVar _ _ a = a

instance Subst Type where
  substPVar x p (ActsFor q r) = ActsFor (substPVar x p q) (substPVar x q r)
  substPVar x p (Says q t) = Says (substPVar x p q) (substPVar x p t)
  substPVar x p (Forall y q t) = Forall y (substPVar x p q) (substPVar x p t)
  substPVar x p (Plus s t) = Plus (substPVar x p s) (substPVar x p t)
  substPVar x p (Times s t) = Times (substPVar x p s) (substPVar x p t)
  substPVar x p (Fn s q t) = Fn (substPVar x p s) (substPVar x p q) (substPVar x p t)
  substPVar _ _ a = a
  substTVar x t (TVar y) | x == y = t
  substTVar x t (Forall y p s) | x /= y = Forall y p (substTVar x t s)
  substTVar x t (Plus s r) = Plus (substTVar x t s) (substTVar x t r)
  substTVar x t (Times s r) = Times (substTVar x t s) (substTVar x t r)
  substTVar x t (Fn s p r) = Fn (substTVar x t s) p (substTVar x t r)
  substTVar x t (Says p s) = Says p (substTVar x t s)
  substTVar _ _ a = a

instance Subst Exp where
  substPVar x p (EActsFor q r) = EActsFor (substPVar x p q) (substPVar x p r)
  substPVar x p (Protect q e) = Protect (substPVar x p q) (substPVar x p e)
  substPVar x p (Lam y t q e) = Lam y (substPVar x p t) (substPVar x p q) (substPVar x p e)
  substPVar x p (LAM y q e) = LAM y (substPVar x p q) (substPVar x p e)
  substPVar x p (App a b) = App (substPVar x p a) (substPVar x p b)
  substPVar x p (Pair a b) = Pair (substPVar x p a) (substPVar x p b)
  substPVar x p (TApp a b) = TApp (substPVar x p a) (substPVar x p b)
  substPVar x p (Project1 a) = Project1 (substPVar x p a)
  substPVar x p (Project2 a) = Project2 (substPVar x p a)
  substPVar x p (Inject1 a b) = Inject1 (substPVar x p a) (substPVar x p b)
  substPVar x p (Inject2 a b) = Inject2 (substPVar x p a) (substPVar x p b)
  substPVar x p (Case e y f z g) = Case (substPVar x p e) y (substPVar x p f) z (substPVar x p g)
  substPVar x p (Bind y f g) = Bind y (substPVar x p f) (substPVar x p g)
  substPVar x p (Assume a b) = Assume (substPVar x p a) (substPVar x p b)
  substPVar _ _ a = a
  substTVar x p (Protect q e) = Protect q (substTVar x p e)
  substTVar x p (Lam y t q e) = Lam y (substTVar x p t) q (substTVar x p e)
  substTVar x p (LAM y q e) | x /= y = LAM y q (substTVar x p e)
  substTVar x p (App a b) = App (substTVar x p a) (substTVar x p b)
  substTVar x p (Pair a b) = Pair (substTVar x p a) (substTVar x p b)
  substTVar x p (TApp a b) = TApp (substTVar x p a) (substTVar x p b)
  substTVar x p (Project1 a) = Project1 (substTVar x p a)
  substTVar x p (Project2 a) = Project2 (substTVar x p a)
  substTVar x p (Inject1 a b) = Inject1 (substTVar x p a) (substTVar x p b)
  substTVar x p (Inject2 a b) = Inject2 (substTVar x p a) (substTVar x p b)
  substTVar x p (Case e y f z g) = Case (substTVar x p e) y (substTVar x p f) z (substTVar x p g)
  substTVar x p (Bind y f g) = Bind y (substTVar x p f) (substTVar x p g)
  substTVar x p (Assume a b) = Assume (substTVar x p a) (substTVar x p b)
  substTVar _ _ a = a

instance (Subst a, Subst b) => Subst (a, b) where
  substPVar x p (a,b) = (substPVar x p a, substPVar x p b)
  substTVar x t (a,b) = (substTVar x t a, substTVar x t b)

instance Subst a => Subst [a] where
  substPVar x p = fmap (substPVar x p)
  substTVar x t = fmap (substTVar x t)

instance Subst a => Subst (Maybe a) where
  substPVar x p = fmap (substPVar x p)
  substTVar x t = fmap (substTVar x t)

instance Subst a => Subst (M.Map k a) where
  substPVar x p = fmap (substPVar x p)
  substTVar x t = fmap (substTVar x t)

instance Subst InferCtx where
  substPVar x p (InferCtx dx' tx' tyc' e' t') = InferCtx (substPVar x p dx')
    (substPVar x p tx') (substPVar x p tyc') (substPVar x p e') (substPVar x p t')
  substTVar x p (InferCtx dx' tx' tyc' e' t') = InferCtx (substTVar x p dx')
    (substTVar x p tx') (substTVar x p tyc') (substTVar x p e') (substTVar x p t')

isFresh :: Text -> Bool
isFresh t = take 3 t == "__f" -- yeah, this is hacky. TODO: do this better

compile :: Prin -> Exp -> Maybe SFLAC
compile pc e = compileWithGivens pc [] e

compileWithGivens :: Prin -> [(Prin, Prin)] -> Exp -> Maybe SFLAC
compileWithGivens pc givens e = do ws <- wanteds pc e
                                   (dx', tx', e') <- inferTypes ws
                                   dx'' <- inferDelegates dx' givens
                                   TC.prove e' (dx'' ++ givens) (M.toList tx') pc

-- TODO: this solver provides a mapping for name -> prin
-- whereas the current proof encoding uses prin -> prin
-- one of those probably should change. consider this a temporary kludge
inferDelegates :: Dx -> [(Prin, Prin)] -> Maybe Dx
inferDelegates dx' givens = fmap (map (\(x,p) -> (PVar x, p)) . M.toList) $
  inferDelegations (const True) givens dx'

inferTypes :: InferCtx -> Maybe (Dx, Tx, Exp)
inferTypes (InferCtx dx' tx' [] exp' _) = Just (dx', tx', exp')
inferTypes (InferCtx dx' tx' ((s,t):tyc') exp' t') =
  subst s t (InferCtx dx' tx' tyc' exp' t') >>= inferTypes

wanteds :: Prin -> Exp -> Maybe InferCtx
wanteds pc e = evalState (runMaybeT $ tc pc e) (FreshVar 0)

fresh :: MonadState FreshVar m => m Text
fresh = do FreshVar i <- get
           _ <- put . FreshVar $ i+1
           return . pack  $ "__f" ++ show (i+1)


freshTy :: MonadState FreshVar m => m Type
freshTy = fmap TVar fresh

freshPr :: MonadState FreshVar m => m Prin
freshPr = fmap PVar fresh

res :: Dx -> Tx -> TyC -> Exp -> Type -> InferState
res a b c d e = pure $ InferCtx a b c d e

mergeTx :: Tx -> Tx -> (Tx, TyC)
mergeTx a b = (M.union a b, M.elems $ M.intersectionWith (,) a b)

merge2 :: InferState -> InferState -> Infer (Dx, Tx, TyC, Exp, Type, Exp, Type)
merge2 as bs = do InferCtx adx atx atyc a' aty <- as
                  InferCtx bdx btx btyc b' bty <- bs
                  let (mtx, mtyc) = mergeTx atx btx
                  return (adx ++ bdx, mtx, atyc ++ btyc ++ mtyc, a', aty, b', bty)

without :: Text -> Tx -> Tx
without x = M.filterWithKey (\k _ -> k /= x)

tc :: Prin -> Exp -> InferState
tc _ EUnit = res [] M.empty [] EUnit Unit
tc _ (Var x) = freshTy >>= \v -> res [] (M.singleton x v) [] (Var x) v
tc _ (EActsFor p q) = res [] M.empty [] (EActsFor p q) (ActsFor p q)
tc pc (App a b) = do (mdx, mtx, mtyc, ae, aty, be, bty) <- merge2 (tc pc a) (tc pc b)
                     fty <- freshTy
                     pc' <- freshPr
                     fty' <- freshTy
                     res (flowsTo pc pc' ++ mdx) mtx
                       ((aty, Fn fty pc' fty'):(fty,bty):mtyc)
                       (App ae be) fty'
tc pc (Pair a b) = do (mdx, mtx, mtyc, ae, aty, be, bty) <- merge2 (tc pc a) (tc pc b)
                      res mdx mtx mtyc (Pair ae be) (Times aty bty)
tc pc (Protect l a) = do InferCtx adx atx atyc ae aty <- tc pc a
                         res (flowsTo pc l ++ adx) atx atyc (Protect l ae) (Says l aty)
tc pc (TApp a t') = do InferCtx adx atx atyc ae (Forall x pc' t) <- tc pc a
                       -- doing this in full generality is possibly undecidable?
                       -- TODO: t' well formed in atx
                       -- TODO: I'm not convinced this is even close to right
                       res (flowsTo pc pc' ++ adx) atx atyc (TApp ae t') (rSubst t x t')
tc pc (Project1 e) = do InferCtx edx etx etyc e' ety <- tc pc e
                        aty <- freshTy
                        bty <- freshTy
                        res edx etx ((ety, Times aty bty):etyc) (Project1 e') aty
tc pc (Project2 e) = do InferCtx edx etx etyc e' ety <- tc pc e
                        aty <- freshTy
                        bty <- freshTy
                        res edx etx ((ety, Times aty bty):etyc) (Project2 e') bty
tc pc (Inject1 e _) = do InferCtx edx etx etyc e' ety <- tc pc e
                         bty <- freshTy
                         res edx etx etyc (Inject1 e' (Just bty)) (Plus ety bty)
tc pc (Inject2 e _) = do InferCtx edx etx etyc e' ety <- tc pc e
                         aty <- freshTy
                         res edx etx etyc (Inject1 e' (Just aty)) (Plus aty ety)
tc pc (Case e x a y b) = do InferCtx edx etx etyc e' ety <- tc pc e
                            InferCtx adx atx atyc a' aty <- tc pc a
                            InferCtx bdx btx btyc b' bty <- tc pc b
                            xty <- freshTy
                            yty <- freshTy
                            let otyc = case (M.lookup x atx, M.lookup y btx) of
                                  (Just xty', Just yty') -> [(xty, xty'), (yty, yty')]
                                  (Just xty', _) -> [(xty, xty')]
                                  (_, Just yty') -> [(yty, yty')]
                                  _ -> []
                            let (mtx, mtyc) = mergeTx etx (without x atx)
                            let (mtx', mtyc') = mergeTx mtx (without y btx)
                            res
                              (edx ++ adx ++ bdx)  mtx'
                              ((ety, Plus xty yty):(aty,bty):
                               etyc ++ atyc ++ btyc ++ mtyc ++ mtyc' ++ otyc)
                              (Case e' x a' y b') aty
tc pc (Bind x a b) = do InferCtx adx atx atyc a' aty <- tc pc a
                        l <- freshPr
                        t <- freshTy
                        InferCtx bdx btx btyc b' bty <- tc (rLub pc l) b
                        let otyc = case M.lookup x btx of
                              Just t' -> [(t,t')]
                              Nothing -> []
                        let (mtx, mtyc) = mergeTx atx (without x btx)
                        res
                          (adx ++ bdx) mtx
                          ((aty, Says l t):atyc ++ btyc ++ mtyc ++ otyc) (Bind x a' b') bty
tc pc (Assume a b) = do InferCtx adx atx atyc a' (ActsFor p q) <- tc pc a
                        -- TODO: again, not sure how to do this in full generality
                        InferCtx bdx btx btyc b' bty <- tc pc b
                        let bdx' = delete (p,q) bdx
                        let (mtx, mtyc) = mergeTx atx btx
                        res
                          (flowsTo pc (Voice q) ++
                             flowsTo (Voice (Conf p)) (Voice (Conf q)) ++
                             adx ++ bdx')
                          mtx (atyc ++ btyc ++ mtyc) (Assume a' b') bty
tc _ (Lam x t pc' e) = do InferCtx edx etx etyc e' t2 <- tc pc' e
                          let otyc = case M.lookup x etx of
                                       Just t1 -> [(t1, t)]
                                       Nothing -> []
                          res edx (without x etx) (otyc ++ etyc)
                            (Lam x t pc' e') (Fn t pc' t2)
tc _ (LAM x pc' e) = do InferCtx edx etx etyc e' ety <- tc pc' e
                        -- TODO: I am even less convinced this is at all correct
                        res edx etx etyc (LAM x pc' e') (Forall x pc' ety)

flowsTo :: Prin -> Prin -> Dx
flowsTo p q = [(Conf q, Conf p), (Integ p, Integ q)]

flowsToType :: Prin -> Type -> Dx
flowsToType _ Unit = []
flowsToType l (Times s t) = flowsToType l s ++ flowsToType l t
flowsToType l (Fn _ pc t) = flowsToType l t ++ flowsTo l pc
flowsToType l (Forall _ pc t) = flowsToType l t ++ flowsTo l pc
flowsToType l (Says l' _) = flowsTo l l'
flowsToType _ _ = [(Bot, Top)] -- TODO: check if this is accurate
