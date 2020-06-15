{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.FLAC.Proof.Solver.ActsFor where

import Language.FLAC.Proof.Solver.Norm
import Data.Maybe  (mapMaybe, catMaybes)
import Data.List (sort, union, nub, find)

{-| 
    A delegation context for deciding actsFor queries. Delegations are split into 
    base delegations between primitive principals, and irreducible delegations that
    involve at least one compound principal.  For example, (a ∧ b ≽ c) and (a ≽ b ∨ c) are 
    each irreducible. 
|-}
data DelCtx v s = Dels {
       base       :: [(Base v s, Base v s)]   -- base delegations 
     , irred      :: [(JNorm v s, JNorm v s)] -- irreducible delegations
     }

{-| Create a delegation context from a list of given delegations.  Delegations in the given list are
    reduced and the transitive closure of (fully) reducible delegations is computed. 
|-}
mkDelegationContext :: forall v s. (Eq v, Eq s) => [(JNorm v s, JNorm v s)] -> DelCtx v s
mkDelegationContext givens =
  let dels@Dels{..} = reduce_givens givens in
    dels{ base = closure principals (base ++ top_bot_edges)}
  where
    top_bot_edges :: [(Base v s, Base v s)]
    top_bot_edges = [ (p, B) | p <- principals ]
                         ++ [ (T, q) | q <- principals ]
    principals :: [Base v s]
    principals = nub (concatMap (\(J ms1, J ms2) ->
                                concatMap (\(M bs) -> bs) (ms1 ++ ms2)) givens)

{-| Transitive closure of base delegations |-}
--From: https://gist.github.com/scvalex/389976
closure :: (Eq v, Eq s) => [Base v s] -> [(Base v s, Base v s)] -> [(Base v s, Base v s)]
closure vs es = go vs es
    where
      go [] es     = es
      go (v:vs) es = go vs (nub (es ++ [(a, d) | (a, b) <- es, (c, d) <- es, b == c]))

{-| Reduce delegations by splitting them into multiple simpler (but equivalent) delegations |-}
reduce_givens :: forall v s. [(JNorm v s, JNorm v s)] -> DelCtx v s
reduce_givens dels = foldr reduceJoinJoin (Dels [] []) dels

-- (a ≽ c ∧ d) reduces to (a ≽ c) and (a ≽ d) 
reduceJoinJoin :: (JNorm v s, JNorm v s) -> DelCtx v s -> DelCtx v s
reduceJoinJoin (sup, (J infs)) dels = foldr (reduceJoinMeet sup) dels infs

reduceJoinMeet :: JNorm v s -> MNorm v s -> DelCtx v s -> DelCtx v s
-- (⊤ ≽ b) is redundant
reduceJoinMeet (J [M [T]]) inf dels = dels
-- (a ≽ b) may reduce 
reduceJoinMeet (J [sup]) inf dels = reduceMeetMeet sup inf dels
-- (a ∧ b ≽ c) is irreducible
--   TODO: unless a == b or a == c, then it is redundant
reduceJoinMeet sup inf dels@Dels{..} = dels{ irred = ((sup,(J [inf])):irred) }

-- (a ∨ b ≽ c) reduces to (a ≽ c) and (b ≽ c) 
reduceMeetMeet :: MNorm v s -> MNorm v s -> DelCtx v s -> DelCtx v s
reduceMeetMeet (M sups) inf dels = foldr (flip reduceBaseMeet inf) dels sups

-- (a ∨ b ≽ c) reduces to (a ≽ c) and (b ≽ c) 
reduceMeetBase :: MNorm v s -> Base v s -> DelCtx v s -> DelCtx v s
reduceMeetBase (M sups) inf dels = foldr (\sup dels'@Dels{..} ->
                                           dels'{ base = ((sup,inf):base)})
                                         dels sups

-- (a ≽ b ∧ c) reduces to (a ≽ b) and (a ≽ c) 
reduceBaseJoin :: Base v s -> JNorm v s -> DelCtx v s -> DelCtx v s
reduceBaseJoin sup (J infs) dels = foldr (reduceBaseMeet sup) dels infs

reduceBaseMeet :: Base v s -> MNorm v s -> DelCtx v s -> DelCtx v s
-- (a ≽ ⊥) is redundant
reduceBaseMeet sup (M []) dels = dels
reduceBaseMeet sup (M [B]) dels = dels
-- (⊤ ≽ a) is redundant
reduceBaseMeet T inf dels = dels
-- (a ≽ b) is reduced
reduceBaseMeet sup (M [inf]) dels@Dels{..} = dels{ base = ((sup,inf):base)}
-- (a ≽ b ∨ c) does not reduce
--   TODO: unless a == b or a == c, then it is redundant
reduceBaseMeet sup inf dels@Dels{..} = dels{ irred = ((J [M [sup]], J [inf]):irred) }

{-| Proof structure for actsfor decisions |-}
data ActsForProof v s =                    
      AFTop
    | AFBot
    | AFRefl 
    | AFDel (Base v s, Base v s) -- NB: this implicitly uses transitivity on given dels
    | AFConj [ActsForProof v s] -- for each RHS q, proof that there is a LHS p s.t. p > q 
    | AFDisj [ActsForProof v s] -- for each RHS q, proof that there is a LHS p s.t. p > q 
    | AFIrred [ActsForProof v s] -- a transitive proof via irreducible predicates

-- Assumption: bounds have already been substituted
actsFor :: forall v s. (Eq v, Eq s) => DelCtx v s -> Norm v s -> Norm v s -> Bool
actsFor delctx p q = actsForJ delctx (conf p) (conf q) && actsForJ delctx (integ p) (integ q)

actsForJ :: forall v s. (Eq v, Eq s) => DelCtx v s -> JNorm v s -> JNorm v s -> Bool
actsForJ delctx (J pms) (J qms) = conjActsFor delctx pms qms

conjActsFor :: forall v s. (Eq v, Eq s)
             => DelCtx v s
             -> [MNorm v s]
             -> [MNorm v s]
             -> Bool
conjActsFor delctx pms [] = True -- p ≽ ⊥
conjActsFor delctx pbs qbs = and $ map (findSupM delctx pbs) qbs

{- findSupM delctx pbs qb: find an superior of qb in pbs -}
findSupM :: forall v s. (Eq v, Eq s)
         => DelCtx v s
         -> [MNorm v s]
         -> MNorm v s
         -> Bool
findSupM delctx [] qb = False
findSupM delctx (pb : pbs) qb = actsForM delctx pb qb || findSupM delctx pbs qb

actsForM :: forall v s. (Eq v, Eq s) => DelCtx v s -> MNorm v s -> MNorm v s -> Bool 
actsForM delctx (M pbs) (M qbs) = disjActsFor delctx pbs qbs

disjActsFor :: forall v s. (Eq v, Eq s)
             => DelCtx v s
             -> [Base v s]
             -> [Base v s]
             -> Bool
disjActsFor delctx [] [] = True
disjActsFor delctx pbs qbs = and $ map (flip (findInfB delctx) qbs) pbs

{- findInfB delctx pb in qbs: find an inferior of pb in qbs -}
findInfB :: forall v s. (Eq v, Eq s)
         => DelCtx v s
         -> Base v s
         -> [Base v s]
         -> Bool
findInfB delctx pb [] = False
findInfB delctx pb (qb : qbs) = actsForB delctx pb qb || findInfB delctx pb qbs


--  if p ≽ a ∧ b and c ∨ d ≽ q, then p ≽ q by transitivity
actsForB :: forall v s. (Eq v, Eq s) => DelCtx v s
         -> Base v s
         -> Base v s
         -> Bool
actsForB delctx p q =
    p == q || findMatch (p,q) (base delctx) || actsForIrred (irred delctx) (base delctx) p q
  where
    findMatch del [] = False
    findMatch del (del':dels) = del == del'
                                || findMatch del dels 

equivB_bool :: forall v s. (Eq v, Eq s) => DelCtx v s
         -> Base v s
         -> Base v s
         -> Bool
equivB_bool delctx p q = (actsForB delctx p q) && (actsForB delctx q p)

equivM_bool :: forall v s. (Eq v, Eq s) => DelCtx v s
         -> MNorm v s
         -> MNorm v s
         -> Bool
equivM_bool delctx p q = (actsForM delctx p q) && (actsForM delctx q p)


equivJ_bool :: forall v s. (Eq v, Eq s) => DelCtx v s
         -> JNorm v s
         -> JNorm v s
         -> Bool
equivJ_bool delctx p q = (actsForJ delctx p q) && (actsForJ delctx q p)

equiv_bool :: forall v s. (Eq v, Eq s) => DelCtx v s
         -> Norm v s
         -> Norm v s
         -> Bool
equiv_bool delctx p q = (actsFor delctx p q) && (actsFor delctx q p)

--  For an irreducible delegation of the form (a ∧ b ≽ c ∨ d),
--  if p ≽ a ∧ b and c ∨ d ≽ q, then p ≽ q by transitivity
--  through the delegation.
actsForIrred :: forall v s. (Eq v, Eq s) =>
            [(JNorm v s, JNorm v s)] -- irreducible delegations
         -> [(Base v s, Base v s)]   -- base delegations 
         -> Base v s
         -> Base v s
         -> Bool
actsForIrred irred_dels base_dels p q =
  case irred_dels of
    (r, J s_ms):irreds -> let p_af_r_ctx = reduceBaseJoin p r emptyCtx in -- XXX: Need try these proof obligations for every irred del
                          let p_af_r = base p_af_r_ctx in
                          let s_af_q_ctx = foldr (flip reduceMeetBase q) emptyCtx s_ms in
                          -- assert : irred s_af_q_ctx == []
                          let s_af_q = base s_af_q_ctx in
                          and $ 
                              ((map (\(t, u) -> 
                                  if (any (== (t,u)) base_dels) then
                                    True
                                  else
                                    actsForIrred irreds base_dels t u)
                                  (p_af_r ++ s_af_q))
                                ++ (map (\del ->
                                        case del of
                                          (J [M [t]], J [M bs]) -> do
                                            if (any (\u -> any (== (t,u)) $ base_dels) bs) then
                                                True
                                              else
                                                False -- TODO: actsForIrred irreds base_dels t bs
                                          -- The following cases should never occur if contexts
                                          -- only represent ⊥ as J [M [B]], but we include them
                                          -- for completeness.
                                          (J [M []], J [M bs]) -> do
                                            any (\u -> any (== (B,u)) $ base_dels) bs -- XXX: actsForIrred case here too.
                                          (J [], J [M bs]) -> do
                                            any (\u -> any (== (B,u)) $ base_dels) bs -- XXX: actsForIrred case here too.
                                          _ -> False)
                                      (irred p_af_r_ctx)))
    _ -> False
 where
   emptyCtx = Dels [] []
-- The following testcase compiles in GHC, but not after hs-to-coq translation
-- test:: [a] -> Maybe [Bool]
-- test as = sequence $ map (\pb -> Just True) as