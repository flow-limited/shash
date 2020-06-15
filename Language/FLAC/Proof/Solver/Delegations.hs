{-# LANGUAGE RankNTypes, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Language.FLAC.Proof.Solver.Delegations where

import Language.FLAC.Syntax.Runtime
import Language.FLAC.Proof.Solver.Norm
import Language.FLAC.Proof.Solver.ActsFor

import Data.Map as M ( Map, foldlWithKey, empty, fromList, unionWith
                     , findWithDefault, union, keys, toList, mapWithKey
                     , keysSet, elems, lookup, singleton, insert)
import UniqSet       (UniqSet, unionManyUniqSets, emptyUniqSet, unionUniqSets,
                       unitUniqSet, nonDetEltsUniqSet)
import Unique (Uniquable(..))
import qualified Data.Set as S    (Set, union, empty, singleton, notMember, toList)
import Data.List                  (partition)


data ActsForCt v s = AFCt { af :: (Norm v s, Norm v s) }

{- Internal type for associating an temporary ID for each constraint -}
data ActsForCt_int v s = AFCt_int {ctid :: Int, afct :: ActsForCt v s }

instance Eq (ActsForCt_int v s) where
  (==) (AFCt_int a _) (AFCt_int b _) = a == b

instance Ord (ActsForCt_int v s) where
  compare (AFCt_int a _) (AFCt_int b _) = compare a b


type Bounds v s = Map v (JNorm v s)

data SolverResult v s
  = Solved (Bounds v s, Bounds v s)
  | Impossible (ActsForCt v s)

data SearchResult v s
  = Win                           -- ^ Two terms are equal
  | Lose (ActsForCt_int v s)       -- ^ Cannot satisfy this constraint
  | ChangeBounds [(v, JNorm v s)] -- ^ Two terms are only equal if the given substitution holds

solveConstraints ::
             forall v s. (Uniquable v, Ord v, Ord s) =>
             (v -> Bool)
             -> [ActsForCt v s] -- ^ givens
             -> [ActsForCt v s] -- ^ wanteds
             -> SolverResult v s
solveConstraints touchable givens wanteds =
    let confSearchCtx = SCtx touchable confDelCtx (mkWakeup confVarToAFDeps) True
        confResult = search confSearchCtx initialBounds [] intWanteds []
        integSearchCtx = SCtx touchable integDelCtx (mkWakeup integVarToAFDeps) False
        integResult = search integSearchCtx initialBounds [] intWanteds []
      in
        case (confResult, integResult) of
          (Lose (AFCt_int _ afct), _) ->
            Impossible afct
          (_, Lose (AFCt_int _ afct)) ->
            Impossible afct
          (cnf, intg) -> Solved ( fromList $ resultBounds cnf
                                , fromList $ resultBounds intg )
  where

    {- Assign an identifier for each AFCt so that cts with the same normalized form get handled appropriately. -}
    intWanteds :: [ActsForCt_int v s]
    intWanteds = map (\(i, afct) -> AFCt_int i afct) $ zip [0..length wanteds] wanteds

    projActsFor :: (Norm v s -> JNorm v s)
                -> ActsForCt v s -> (JNorm v s, JNorm v s)
    projActsFor proj (AFCt (p, q)) = (proj p, proj q)

    confDelCtx :: DelCtx v s
    confDelCtx = mkDelegationContext (map (projActsFor conf) givens)

    integDelCtx :: DelCtx v s
    integDelCtx = mkDelegationContext (map (projActsFor conf) givens)

    allVars :: [v]
    allVars = concat [nonDetEltsUniqSet $
                fvNorm p `unionUniqSets` fvNorm q | (AFCt (p, q)) <- wanteds]

    initialBounds :: Map v (JNorm v s)
    initialBounds = fromList $ map (\v -> (v, J [M [B]]))
                            $ [v | v <- allVars, touchable v]

    resultBounds (ChangeBounds bnds) = bnds
    resultBounds Win = []
    resultBounds (Lose af) = error "should not happen"

    confAFToVarDeps :: Map (ActsForCt_int v s) [v]
    confAFToVarDeps = fromList $ map (\afct@(AFCt_int _ (AFCt (_, N conf _))) -> (afct, touchableFVs conf)) $ intWanteds

    confVarToAFDeps :: Map v (S.Set (ActsForCt_int v s))
    confVarToAFDeps = invert confAFToVarDeps

    integAFToVarDeps :: Map (ActsForCt_int v s) [v]
    integAFToVarDeps = fromList $ map (\afct@(AFCt_int _ (AFCt (_, N _ integ))) -> (afct, touchableFVs integ)) $ intWanteds

    integVarToAFDeps :: Map v (S.Set (ActsForCt_int v s))
    integVarToAFDeps = invert integAFToVarDeps

    invert :: Map (ActsForCt_int v s) [v] -> Map v (S.Set (ActsForCt_int v s))
    invert afToVarDeps = foldl (\deps (afct, vars) ->
                              unionWith (S.union) (fromList [(v, S.singleton afct) | v <- vars]) deps)
                            empty $ toList afToVarDeps

    touchableFVs p = [ v | v <- nonDetEltsUniqSet $ fvJNorm p, touchable v ]

    mkWakeup :: Map v (S.Set (ActsForCt_int v s)) -> Wakeup v s
    mkWakeup varToDeps solved chg = let eqns = foldl (\deps v ->
                                                   (findWithDefault S.empty v varToDeps) `S.union` deps)
                                                S.empty
                                                chg
                                    in partition (\eq -> (S.notMember eq eqns)) solved
{-
-}

type Wakeup v s =
  [ActsForCt_int v s]
  -> [v]
  -> ([ActsForCt_int v s], [ActsForCt_int v s])

data SearchContext v s = SCtx { substOk :: (v -> Bool)
                                 , delctx  :: DelCtx v s
                                 , wakeup  :: Wakeup v s
                                 , isConf  :: Bool
                                 }

search :: forall v s. (Uniquable v, Ord v, Ord s) =>
       SearchContext v s
       -> Bounds v s
       -> [ActsForCt_int v s]
       -> [ActsForCt_int v s]
       -> [(v, JNorm v s)]
       -> SearchResult v s
search _ _ _ [] changes = case changes of
                          [] -> Win
                          _ -> ChangeBounds changes
search ctx@SCtx{..} bounds solved
         (af@(AFCt_int _ (AFCt ((u@(N cp ip)), (v@(N cq iq))))):iafs) changes =
    -- solve on uninstantiated vars. return updated bounds
    let sr = refineBoundsIfNeeded
    in case sr of
       Win -> search ctx bounds (af:solved) iafs changes
       Lose af' -> Lose af'
       ChangeBounds bnds ->
         -- update bounds and re-solve: this ensures all members of solved are only added via 'Win'
         let new_bounds = union (fromList bnds) bounds
             vchgd = map fst bnds
             (solved', to_awake) = wakeup solved vchgd
         in search ctx new_bounds solved' (af:(to_awake ++ iafs)) (bnds ++ changes)
  where
    refineBoundsIfNeeded :: SearchResult v s
    refineBoundsIfNeeded =
      let p       = if isConf then cp else ip
          q       = if isConf then cq else iq
          p'      = substJNorm substOk bounds isConf p
          q'      = substJNorm substOk bounds isConf q
          sub_delctx = substDelCtx substOk bounds isConf delctx
      -- XXX: l bounded with a \/ b doesn't act for a \/ b (?)
      in if actsForJ sub_delctx p' q' then
          Win
         else
          case substOkVars substOk p of
            [] -> Lose af
            [var] -> case joinWith q (findWithDefault (J [M [B]]) var bounds) of
                       Just bnd -> ChangeBounds [(var, bnd)]
                       Nothing -> Lose af
            vars -> let tryvar vs = case vs of
                          [] -> Lose af
                          (v:vs') -> case joinWith q (findWithDefault (J [M [B]]) v bounds) of
                                      Just bnd ->
                                        -- so far so good. recurse with this bound set.
                                        let new_bounds = insert v bnd bounds
                                        in case search ctx new_bounds solved (af:iafs) [] of
                                             -- couldn't solve, try next vars
                                             Lose af -> tryvar vs'
                                             -- solved with this change, return it
                                             Win -> ChangeBounds [(v, bnd)]
                                             -- solved with this and other changes, return them
                                             ChangeBounds changes -> ChangeBounds ((v, bnd):changes)
                                      Nothing -> tryvar vs'
                    in tryvar vars

substOkVars :: Uniquable v => (v -> Bool) -> JNorm v s -> [v]
substOkVars substOk p = [ v | v <- nonDetEltsUniqSet $ fvJNorm p, substOk v ]

{-| For each substitutable variable in a DelCtx, substitute its bound and renormalize. |-}
substDelCtx :: (Ord v, Ord s) => (v -> Bool) -- ^ Predicate for susbtitutable vars
           -> Bounds v s -- ^ Variable bounds
           -> Bool       -- ^ Is Context a confidentiality context?
           -> DelCtx v s  -- ^ Context to perform substitution on
           -> DelCtx v s
substDelCtx substOk bounds isConf delctx@Dels{..} =
    let sub_base  = [ (goSB p, goSB q) | (p,q) <- base ]
        sub_irred = [ (goSJ p, goSJ q) | (p,q) <- irred ] in
      mkDelegationContext (sub_base ++ sub_irred)
  where
    goSB = substBase substOk bounds isConf
    goSJ = substJNorm substOk bounds isConf

{-| For each substitutable variable in a JNorm, substitute its bound and renormalize. |-}
substJNorm :: (Ord v, Ord s) => (v -> Bool) -- ^ Predicate for susbtitutable vars
           -> Bounds v s -- ^ Variable bounds
           -> Bool       -- ^ Is JNorm a confidentiality policy?
           -> JNorm v s  -- ^ JNorm to perform substitution on
           -> JNorm v s
substJNorm substOk bounds isConf (J (m:ms)) = foldr mergeJNormJoin
                                                    (substMNorm substOk bounds isConf m)
                                                    (map (substMNorm substOk bounds isConf) ms)
substJNorm substOk bounds isConf (J []) = J [M [B]]

{-| For each substitutable variable in a MNorm, substitute its bound and renormalize. |-}
substMNorm :: (Ord v, Ord s) =>  (v -> Bool) -> Bounds v s -> Bool -> MNorm v s -> JNorm v s
substMNorm substOk bounds isConf (M (b:bs)) = foldr mergeJNormMeet
                                                    (substBase substOk bounds isConf b)
                                                    (map (substBase substOk bounds isConf) bs)
substMNorm substOk bounds isConf (M []) = J [M [B]]

{-| If Base contains a substitutable variable, replace it with its bound. |-}
substBase :: (Ord v, Ord s) => (v -> Bool) -> Bounds v s -> Bool -> Base v s -> JNorm v s
substBase _ _ _ B = J [M [B]]
substBase _ _ _ T = J [M [T]]
substBase _ _ _ (P s) = J [M [(P s)]]
substBase _ _ _ (U s) = J [M [(U s)]]
substBase substOk bounds isConf (V tv) =
  if substOk tv then
    findWithDefault (J [M [B]]) tv bounds
  else
    J [M [V tv]]
substBase substOk bounds isConf (VarVoice tv) =
  if substOk tv then
    if isConf then
      (J [M [B]])
    else
      integ (voiceOf (N (findWithDefault (J [M [B]]) tv bounds) (J [M [B]])))
  else
    J [M [VarVoice tv]]
substBase substOk bounds isConf (VarEye tv) =
  if substOk tv then
    if isConf then
      conf (eyeOf (N (J [M [B]]) (findWithDefault (J [M [B]]) tv bounds)))
    else
      (J [M [B]])
  else
    J [M [VarEye tv]]
substBase substOk bounds isConf (UVoice t) = J [M [UVoice t]]
substBase substOk bounds isConf (UEye t) = J [M [UEye t]]

{-| Collect the free variables of a normalized principal -}
fvNorm :: (Uniquable v) => Norm v s -> UniqSet v
fvNorm (N conf integ) = fvJNorm conf `unionUniqSets` fvJNorm integ

-- | Find the 'v' in a 'CoreJNorm'
fvJNorm :: (Uniquable v) => JNorm v s -> UniqSet v
fvJNorm = unionManyUniqSets . map fvMNorm . unJ

fvMNorm :: (Uniquable v) => MNorm v s -> UniqSet v
fvMNorm = unionManyUniqSets . map fvBase . unM

fvBase :: (Uniquable v) => Base v s -> UniqSet v
fvBase (P _) = emptyUniqSet
fvBase (U _) = emptyUniqSet
fvBase B     = emptyUniqSet
fvBase T     = emptyUniqSet
fvBase (V v)        = unitUniqSet v
fvBase (VarVoice v) = unitUniqSet v
fvBase (VarEye v)   = unitUniqSet v
fvBase (UVoice _)   = emptyUniqSet
fvBase (UEye _)     = emptyUniqSet
