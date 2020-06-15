{-# LANGUAGE GADTs, DataKinds, ConstraintKinds, TypeOperators, TypeFamilies, TypeApplications, ScopedTypeVariables, PolyKinds, StandaloneKindSignatures, UndecidableInstances, TemplateHaskell, StandaloneDeriving, FlexibleContexts, AllowAmbiguousTypes #-}

module Language.FLAC.Proof where

import Language.FLAC.Syntax
import Language.FLAC.Syntax.TH
import Language.FLAC.Syntax.Promoted
import qualified Language.FLAC.Syntax.Runtime as R
import qualified Data.Text as T

import Control.Monad.Trans.Class (lift)
import Data.Singletons
import Data.Singletons.TH
import Data.Singletons.TH.Options
import Data.Singletons.Prelude.List
import Data.Singletons.Prelude.Tuple
import Data.Singletons.Prelude.Bool
import GHC.TypeLits

type Typed = (Symbol, Type)
type Delegation = (Prin, Prin)

$(withOptions promotionOptions $ singletons $ lift [d|
  remove :: Eq a => a -> [(a,b)] -> [(a,b)]
  remove _ [] = []
  remove a ((b,d):bs) = if (a == b) then remove a bs else (b,d):(remove a bs)

  subst :: Type -> Symbol -> Type -> Type
  subst v@(TVar x) y t = if (x == y) then t else v
  subst (Forall x p t) y t' = if (x == y) then Forall x p t else Forall x p (subst t y t')
  subst (Plus t1 t2) x t = Plus (subst t1 x t) (subst t2 x t)
  subst (Times t1 t2) x t = Times (subst t1 x t) (subst t2 x t)
  subst (Fn t1 p t2) x t' = Fn (subst t1 x t') p (subst t2 x t')
  subst (Says p t) x t' = Says p (subst t x t')
  subst (ActsFor p q) _ _ = ActsFor p q
  subst Unit _ _ = Unit

  lub :: Prin -> Prin -> Prin
  lub p q = Conj (Conf (Conj p q)) (Integ (Disj p q))

  -- we can't singleton anything with overlapping guards
  -- which is why this is so awkwardly written
  delegates :: [(Prin, Prin)] -> Prin -> Prin -> Bool
  delegates dx a b = b == Bot || a == Top || a == b ||
            unConf a (\a' -> unConf b (\b' -> delegates dx a' b')) ||
            unInteg a (\a' -> unInteg b (\b' -> delegates dx a' b')) ||
            unConj a (\p1 p2 -> delegates dx p1 b || delegates dx p2 b) ||
            unConj b (\q1 q2 -> delegates dx a q1 && delegates dx a q2) ||
            unDisj a (\p1 p2 -> delegates dx p1 b && delegates dx p2 b) ||
            unDisj b (\q1 q2 -> delegates dx a q1 || delegates dx a q2) ||
            any (\c -> delegates dx c b) (map snd (filter (\(m,_) -> m == a) dx))
    where unConf (Raw _) _ = False
          unConf (PVar _) _ = False
          unConf Top _ = False
          unConf Bot _ = False
          unConf (Integ _) _ = False
          unConf (Conf p) f = f p
          unConf (Conj _ _) _ = False
          unConf (Disj _ _) _ = False
          unConf (Voice _) _ = False
          unConf (Eye _) _ = False
          unInteg (Raw _) _ = False
          unInteg (PVar _) _ = False
          unInteg Top _ = False
          unInteg Bot _ = False
          unInteg (Integ p) f = f p
          unInteg (Conf _) _ = False
          unInteg (Conj _ _) _ = False
          unInteg (Disj _ _) _ = False
          unInteg (Voice _) _ = False
          unInteg (Eye _) _ = False
          unConj (Raw _) _ = False
          unConj (PVar _) _ = False
          unConj Top _ = False
          unConj Bot _ = False
          unConj (Integ _) _ = False
          unConj (Conf _) _ = False
          unConj (Conj p q) f = f p q
          unConj (Disj _ _) _ = False
          unConj (Voice _) _ = False
          unConj (Eye _) _ = False
          unDisj (Raw _) _ = False
          unDisj (PVar _) _ = False
          unDisj Top _ = False
          unDisj Bot _ = False
          unDisj (Integ _) _ = False
          unDisj (Conf _) _ = False
          unDisj (Conj _ _) _ = False
          unDisj (Disj p q) f = f p q
          unDisj (Voice _) _ = False
          unDisj (Eye _) _ = False

  delegatesType :: [(Prin, Prin)] -> Prin -> Type -> Bool
  delegatesType _  _ Unit = True
  delegatesType dx l (Times s t) = delegatesType dx l s && delegatesType dx l t
  delegatesType dx l (Fn _ pc t) = delegatesType dx l t && delegates dx l pc
  delegatesType dx l (Forall _ pc t) = delegatesType dx l t && delegates dx l pc
  delegatesType dx l (Says l' _) = delegates dx l l'
  delegatesType _ _ (ActsFor _ _) = False
  delegatesType _ _ (Plus _ _) = False
  delegatesType _ _ (TVar _) = False -- TODO: check these three cases
                                                     |])

type ActsFor (dx :: [Delegation]) (a :: Prin) (b :: Prin) = Delegates dx a b ~ 'True
type FlowsTo (dx :: [Delegation]) (a :: Prin) (b :: Prin) = (Delegates dx ('Conf b) ('Conf a) ~ 'True, Delegates dx ('Integ a) ('Integ b) ~ 'True)
type FlowsToType (dx :: [Delegation]) (a :: Prin) (t :: Type) =
  DelegatesType dx a t ~ 'True

data FLAC
  (delctx :: [Delegation])
  (typctx :: [Typed])
  (pc :: Prin) (typ :: Type) where
  EUnit :: FLAC dx tx pc 'Unit
  Var :: Lookup x tx ~ 'Just t => Sing (x :: Symbol) -> FLAC dx tx pc t
  Del :: Sing p -> Sing q -> FLAC dx tx pc ('ActsFor p q)
  Lambda :: Lookup x tx ~ 'Just t =>
    Sing (x :: Symbol) -> Sing (t :: Type) -> Sing (pc' :: Prin)
    -> FLAC dx tx pc' t2
    -> FLAC dx (Remove x tx) pc ('Fn t pc' t2)
  -- is this what TLam implies? X free in gamma?
  TLambda :: Lookup x tx ~ 'Nothing =>
    Sing (x :: Symbol) -> Sing (pc' :: Prin)
    -> FLAC dx tx pc' t
    -> FLAC dx tx pc ('Forall x pc' t)
  App :: FlowsTo dx pc pc' =>
    FLAC dx tx pc ('Fn t1 pc' t2)
    -> FLAC dx tx pc t1
    -> FLAC dx tx pc t2
  -- require t' well-formed in dx
  TApp :: FlowsTo dx pc pc' =>
    FLAC dx tx pc ('Forall x pc' t) -> Sing (t' :: Type) -> FLAC dx tx pc (Subst t x t')
  Pair :: FLAC dx tx pc t1 -> FLAC dx tx pc t2 -> FLAC dx tx pc ('Times t1 t2)
  Project1 :: FLAC dx tx pc ('Times t1 t2) -> FLAC dx tx pc t1
  Project2 :: FLAC dx tx pc ('Times t1 t2) -> FLAC dx tx pc t2
  Inject1 :: FLAC dx tx pc t1 -> FLAC dx tx pc ('Plus t1 t2)
  Inject2 :: FLAC dx tx pc t2 -> FLAC dx tx pc ('Plus t1 t2)
  Case :: (tx1 ~ ('(x, t1) ': tx), tx2 ~ ('(y, t2) ': tx), FlowsToType dx pc t) =>
    FLAC dx tx pc ('Plus t1 t2)
    -> Sing (x :: Symbol) -> FLAC dx tx1 pc t
    -> Sing (y :: Symbol) -> FLAC dx tx2 pc t
    -> FLAC dx tx pc t
  UnitM :: FlowsTo dx pc l =>
    Sing (l :: Prin) -> FLAC dx tx pc t -> FLAC dx tx pc ('Says l t)
  -- do we end up needing this?
  -- SEALED :: FLAC dx tx pc ('Var v) t -> FLAC dx tx pc ('Protect l ('Var v)) ('Says l t)
  Bind :: (tx' ~ ('(x, t') ': tx), FlowsToType dx (Lub pc l) t) =>
    Sing (x :: Symbol) -> FLAC dx tx pc ('Says l t') -> FLAC dx tx' (Lub pc l) t
    -> FLAC dx tx pc t
  Assume :: (dx' ~ ('(p, q) ': dx), -- is this what goes into dx?
             ActsFor dx pc ('Voice q), ActsFor dx ('Voice ('Conf p)) ('Voice ('Conf q))) =>
    FLAC dx tx pc ('ActsFor p q)
    -> FLAC dx' tx pc t
    -> FLAC dx tx pc t

deriving instance Show (FLAC dx tx pc t)

data SFLAC where
  SFLAC :: Sing (dx :: [Delegation])
        -> Sing (tx :: [Typed])
        -> Sing (p :: Prin)
        -> Sing (t :: Type) -> FLAC dx tx p t -> SFLAC

deriving instance Show SFLAC

rSubst :: R.Type -> T.Text -> R.Type -> R.Type
rSubst t x t' = withSomeSing t $ \st ->
                  withSomeSing x $ \sx ->
                    withSomeSing t' $ \st' ->
                      fromSing (sSubst st sx st')

rLub :: R.Prin -> R.Prin -> R.Prin
rLub p q = withSomeSing p $ \sp ->
             withSomeSing q $ \sq ->
                fromSing (sLub sp sq)
