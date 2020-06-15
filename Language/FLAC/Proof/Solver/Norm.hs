{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}
module Language.FLAC.Proof.Solver.Norm where

-- External
import Data.Either   (partitionEithers, isLeft)
import Data.List     (union, nub, sort)
import Data.Text     (Text)
import Language.FLAC.Syntax.Runtime
--import Control.Monad.Fix
--import Data.Graph    (graphFromEdges, reachable, vertices)

pttp :: Prin -> TypePrin Text Text
pttp (Raw x) = PT_Name x
pttp (PVar x) = PT_Var x
pttp Top = PT_Top
pttp Bot = PT_Bot
pttp (Integ p) = PT_Integ (pttp p)
pttp (Conf p) = PT_Conf (pttp p)
pttp (Conj p q) = PT_Conj (pttp p) (pttp q)
pttp (Disj p q) = PT_Disj (pttp p) (pttp q)
pttp (Voice p) = PT_Voice (pttp p)
pttp (Eye p) = PT_Eye (pttp p)

tptp :: TypePrin Text Text -> Prin
tptp (PT_Name x) = Raw x
tptp (PT_Var x) = PVar x
tptp PT_Top = Top
tptp PT_Bot = Bot
tptp (PT_Integ p) = Integ (tptp p)
tptp (PT_Conf p) = Conf (tptp p)
tptp (PT_Conj p q) = Conj (tptp p) (tptp q)
tptp (PT_Disj p q) = Disj (tptp p) (tptp q)
tptp (PT_Voice p) = Voice (tptp p)
tptp (PT_Eye p) = Eye (tptp p)
tptp (PT_Uninterp s) = PVar s -- TODO: check this

toNorm :: Prin -> Norm Text Text
toNorm = normPrin . pttp

toPrin :: Norm Text Text -> Prin
toPrin = tptp . reifyNorm

jToPrin :: JNorm Text Text -> Prin
jToPrin = tptp . reifyJNorm

{-| Base principals -}
data Base v s
  =
  P s -- ^ Primitive principal
  | T   -- ^ Top
  | B   -- ^ Bottom
  | V v -- ^ Type var
  | VarVoice v -- ^ Voice of type var
  | VarEye v -- ^ Eye of type var
  | U s -- ^ Uninterpreted type
  | UVoice s -- ^ Voice of uninterpreted type
  | UEye   s -- ^ Eye of uninterpreted type
  deriving Eq

{- Compare function for Base principals -}
-- hs-to-coq chokes on the auto-derived instance,
--  so we have to define this explicitly.
base_compare :: (Ord v, Ord s) => Base v s  -> Base v s -> Ordering
base_compare x y =
  case x of 
    P s1 ->
      case y of
        P s2 -> compare s1 s2 
        _ -> LT
    U s1 ->
      case y of
        P _  -> GT
        U s2 -> compare s1 s2
        _    -> LT
    V v1 -> 
      case y of
        P _  -> GT
        U _  -> GT
        V v2 -> compare v1 v2 
        _    -> LT
    B ->
      case y of
        P _  -> GT
        U _  -> GT
        V _  -> GT
        B    -> EQ
        _    -> LT
    T ->
      case y of
        P _  -> GT
        U _  -> GT
        V _  -> GT
        B    -> GT
        T    -> EQ
        _    -> LT
    VarVoice v1 ->
      case y of
        P _  -> GT
        U _  -> GT
        V _  -> GT
        B    -> GT
        T    -> GT
        VarVoice v2 -> compare v1 v2
        _    -> LT
    VarEye v1 ->
      case y of
        P _  -> GT
        U _  -> GT
        V _  -> GT
        B    -> GT
        T    -> GT
        VarVoice _ -> GT
        VarEye v2  -> compare v1 v2
        _    -> LT
    UVoice v1 ->
      case y of
        P _  -> GT
        U _  -> GT
        V _  -> GT
        B    -> GT
        T    -> GT
        VarVoice _ -> GT
        VarEye   _ -> GT
        UVoice v2  -> compare v1 v2
        _    -> LT
    UEye v1 ->
      case y of
        P _  -> GT
        U _  -> GT
        V _  -> GT
        B    -> GT
        T    -> GT
        VarVoice _ -> GT
        VarEye   _ -> GT
        UVoice   _ -> GT
        UEye v2 -> compare v1 v2

instance (Ord v, Ord s) => Ord (Base v s) where
  compare = base_compare

{-| MNorm is a meet of Base principals -}
newtype MNorm v s = M { unM :: [Base v s]}

instance (Eq v, Eq s) => Eq (MNorm v s) where
{-  (M []) == (M [B]) = True
  (M [B]) == (M []) = True -}
  (M bs1) == (M bs2) = bs1 == bs2

instance (Ord v, Ord c) => Ord (MNorm v c) where
  compare (M [x])   (M [y])   = compare x y
  compare (M [_])   (M (_:_)) = LT
  compare (M (_:_)) (M [_])   = GT
  compare (M xs)    (M ys)    = compare xs ys

{-| JNorm is a join of MNorms -}
newtype JNorm v s = J { unJ :: [MNorm v s]}

instance (Eq v, Eq s) => Eq (JNorm v s) where
{-
  (J []) == (J [M [B]]) = True
  (J [M [B]]) == (J [M []]) = True
  (J [M []]) == (J []) = True
-}
  (J ms1) == (J ms2) = ms1 == ms2

instance (Ord v, Ord s) => Ord (JNorm v s) where
  compare (J [x])   (J [y])   = compare x y
  compare (J [_])   (J (_:_)) = LT
  compare (J (_:_)) (J [_])   = GT
  compare (J xs)    (J ys)    = compare xs ys

{-| A Norm principal is made of a JNorm for confidentiality and a JNorm for integrity -}
data Norm v s = N {conf :: JNorm v s, integ :: JNorm v s}

instance (Eq v, Eq s) => Eq (Norm v s) where
  N c1 i1 == N c2 i2 = c1 == c2 && i1 == i2

instance (Ord v, Ord s) => Ord (Norm v s) where
  compare (N c1 i1) (N c2 i2) =
          case compare c1 c2 of
            GT -> GT
            EQ -> compare i1 i2
            LT -> LT

bases :: forall v s. (Eq v, Eq s) => JNorm v s -> [Base v s]
bases (J ms) = nub $ (concatMap unM ms ++ [T,B])

unEither :: Either a a -> a
unEither (Left a) = a
unEither (Right a) = a

-- | Merge two symbols of a Meet term
--
-- Performs the following rewrites:
--
-- @
-- ⊤ ∨ x    ==>  x
-- x ∨ ⊤    ==>  x
-- x ∨ ⊥    ==>  0
-- ⊥ ∨ x    ==>  0
-- x ∨ x    ==>  x
-- @
mergeWithB :: (Eq v, Eq c) => [Base v c] -> [Base v c]
mergeWithB []      = []
mergeWithB (f:fs) = let eithers = map (`mergeB` f) fs in
                    if not $ any isLeft eithers then
                      f : mergeWithB fs
                    else
                      mergeWithB (map unEither eithers)

mergeB :: (Eq v, Eq c) => Base v c -> Base v c
       -> Either (Base v c) (Base v c)
mergeB T r = Left r       -- ⊤ ∨ x ==> x
mergeB l T = Left l       -- x ∨ ⊤ ==> x
mergeB B _ = Left B       -- ⊥ ∨ x ==> ⊥
mergeB _ B = Left B       -- x ∨ ⊥ ==> ⊥
mergeB l r                -- y ∨ y ==> y
  | l == r = Left l
mergeB l _ = Right l

-- | Merge two components of a Join term
--
-- Performs the following rewrites:
--
-- @
-- ⊤ ∧ x       ==>  ⊤ 
-- x ∧ ⊤       ==>  ⊤
-- ⊥ ∧ x       ==>  x
-- x ∧ ⊥       ==>  x
-- x ∧ (x ∨ y) ==>  x  (Absorbtion)
-- (x ∨ y) ∧ x ==>  x  (Absorbtion)
-- @
mergeWithM :: (Eq v, Eq c) => [MNorm v c] -> [MNorm v c]
mergeWithM []      = []
mergeWithM (f:fs) = let eithers = map (`mergeM` f) fs in
                    if not $ any isLeft eithers then
                      f : mergeWithM fs
                    else
                      mergeWithM (map unEither eithers)

mergeM :: (Eq v, Eq c) => MNorm v c -> MNorm v c
       -> Either (MNorm v c) (MNorm v c)
mergeM (M [T]) _ = Left (M [T])                   -- ⊤ ∧ x       ==>  ⊤ 
mergeM _ (M [T]) = Left (M [T])                   -- x ∧ ⊤       ==>  ⊤ 
mergeM (M (B:_)) r = Left r                       -- ⊥ ∧ x       ==>  x 
mergeM l (M (B:_)) = Left l                       -- x ∧ ⊥       ==>  x
mergeM (M [l]) (M rs) | elem l rs = Left (M [l])  -- x ∧ (x ∨ y) ==>  x
mergeM (M ls) (M [r]) | elem r ls = Left (M [r])  -- (x ∨ y) ∧ x  ==>  x
mergeM l r | l == r = Left l                      -- y ∧ y    ==>  y
mergeM l _ = Right l

zeroM :: MNorm v c -> Bool
zeroM (M (B:_)) = True
zeroM _         = False

{-
mkNonEmpty :: JNorm v c -> JNorm v c
mkNonEmpty (J []) = J [M [B]]
mkNonEmpty s      = s
-}
mkNonEmpty :: JNorm v c -> JNorm v c
mkNonEmpty = id

-- | Simplifies SOP terms using
-- * 'mergeM'
-- * 'mergeB'
simplifyJNorm :: (Ord v, Ord c) => JNorm v c -> JNorm v c
simplifyJNorm = mkNonEmpty
       . J
       . sort . filter (not . zeroM)
       . mergeWithM
       . map (M . sort . mergeWithB . unM)
       . unJ
{-# INLINEABLE simplifyJNorm #-}

reduceBot :: (Ord v, Ord s) => [Base v s] -> [Base v s]
reduceBot bs = if any (== B) bs then [B] else bs


dropDup :: (Ord v, Ord s) => [Base v s] -> [Base v s]
dropDup = nub
{-
dropDup []     = []
dropDup (b:bs) = uniq (sort (b:bs))
 where  uniq [] = []
        uniq (b:bs) = case bs of
                     [] -> [b]
                     (b':_) -> if (b == b' || b == T) then uniq bs
                               else b:(uniq bs)
-}
-- | Merge two JNorm terms by join
mergeJNormJoin :: (Ord v, Ord c) => JNorm v c -> JNorm v c -> JNorm v c
mergeJNormJoin (J ms1) (J ms2) = simplifyJNorm $ J (ms1 ++ ms2)
{-# INLINEABLE mergeJNormJoin #-}

-- | Merge two JNorm terms by meet
mergeJNormMeet :: (Ord v, Ord c) => JNorm v c -> JNorm v c -> JNorm v c
mergeJNormMeet (J ms1) (J ms2)
  = simplifyJNorm
  . J
  $ concatMap (zipWith (\p1 p2 -> M (unM p1 ++ unM p2)) ms1 . replicate (length ms1)) ms2
{-# INLINEABLE mergeJNormMeet #-}

-- | Merge two Norm terms by join
mergeNormJoin :: (Ord v, Ord c) => Norm v c -> Norm v c -> Norm v c
mergeNormJoin (N c1 i1) (N c2 i2) = N (mergeJNormJoin c1 c2) (mergeJNormJoin i1 i2)
{-# INLINEABLE mergeNormJoin #-}

-- | Merge two Norm terms by meet
mergeNormMeet :: (Ord v, Ord c) => Norm v c -> Norm v c -> Norm v c
mergeNormMeet (N c1 i1) (N c2 i2) = N (mergeJNormMeet c1 c2) (mergeJNormMeet i1 i2)
{-# INLINEABLE mergeNormMeet #-}

data TypePrin v s = 
    PT_Top
  | PT_Bot
  | PT_Var v
  | PT_Name s
  | PT_Conf (TypePrin v s)
  | PT_Integ (TypePrin v s)
  | PT_Voice (TypePrin v s)
  | PT_Eye (TypePrin v s)
  | PT_Conj (TypePrin v s) (TypePrin v s)
  | PT_Disj (TypePrin v s) (TypePrin v s)
  | PT_Uninterp s

prinType_eq :: (Eq v, Eq s) => TypePrin v s -> TypePrin v s -> Bool
prinType_eq PT_Top PT_Top = True
prinType_eq PT_Bot PT_Bot = True
prinType_eq (PT_Var var) (PT_Var var') = var == var'
prinType_eq (PT_Name n) (PT_Name n') = n == n'
prinType_eq (PT_Conf p) (PT_Conf q) = prinType_eq p q
prinType_eq (PT_Integ p) (PT_Integ q) = prinType_eq p q
prinType_eq (PT_Voice p) (PT_Voice q) = prinType_eq p q
prinType_eq (PT_Eye p) (PT_Eye q) = prinType_eq p q
prinType_eq (PT_Conj p q) (PT_Conj p' q') = prinType_eq p p' && prinType_eq q q'
prinType_eq (PT_Disj p q) (PT_Disj p' q') = prinType_eq p p' && prinType_eq q q'
prinType_eq (PT_Uninterp n) (PT_Uninterp n') = n == n'
prinType_eq _ _ = False

instance (Eq v, Eq s) => Eq (TypePrin v s) where
  p == q = prinType_eq p q

normPrin :: (Ord v, Ord s) => TypePrin v s -> Norm v s
normPrin (PT_Var v)       = N (J [M [V v]]) (J [M [V v]])
normPrin PT_Top           = N (J [M [T]]) (J [M [T]])
normPrin PT_Bot           = N (J [M [B]]) (J [M [B]])
normPrin (PT_Name x)      = N (J [M [P x]]) (J [M [P x]])
normPrin (PT_Conf x)      = N (jnormPrin True x) (J [M [B]])
normPrin (PT_Integ x)     = N (J [M [B]]) (jnormPrin False x)
normPrin (PT_Voice x)     = voiceOf $ normPrin x
normPrin (PT_Eye x)       = eyeOf $ normPrin x
normPrin (PT_Conj x y)    = mergeNormJoin (normPrin x) (normPrin y)
normPrin (PT_Disj x y)    = mergeNormMeet (normPrin x) (normPrin y) 
normPrin (PT_Uninterp ty) = N (J [M [U ty]]) (J [M [U ty]])

jnormPrin :: (Ord v, Ord s) => Bool -> TypePrin v s -> JNorm v s
jnormPrin isConf (PT_Var v) = J [M [V v]]
jnormPrin isConf PT_Top = J [M [T]]
jnormPrin isConf PT_Bot = J [M [B]]
jnormPrin isConf (PT_Name x) = J [M [P x]]
jnormPrin isConf (PT_Conf x) =
    if isConf then jnormPrin isConf x else J [M [B]]
jnormPrin isConf (PT_Integ x) =
    if isConf then J [M [B]] else jnormPrin isConf x
jnormPrin isConf (PT_Voice x) =
    if isConf then J [M [B]] else integ $ voiceOf $ normPrin x
jnormPrin isConf (PT_Eye x) =
    if isConf then conf $ eyeOf $ normPrin x else J [M [B]]
jnormPrin isConf (PT_Conj x y) = mergeJNormJoin (jnormPrin isConf x) (jnormPrin isConf y)
jnormPrin isConf (PT_Disj x y) = mergeJNormMeet (jnormPrin isConf x) (jnormPrin isConf y)
jnormPrin isConf (PT_Uninterp ty) = (J [M [U ty]])

voiceOf :: (Ord v, Ord s) => Norm v s -> Norm v s
voiceOf (N conf integ) = N (J [M [B]]) (mergeJNormJoin (wrapVars conf) integ)
  where
    wrapVars (J ms) = J (map wrapVars' ms)
    wrapVars' (M bs) = M (map wrapVars'' bs)
    wrapVars'' (V v) = VarVoice v 
    wrapVars'' (VarVoice v) = VarVoice v 
    wrapVars'' (VarEye v) = (V v)
    wrapVars'' (UVoice s) = UVoice s
    wrapVars'' (UEye   s) = (U s)
    wrapVars'' p = p
  
eyeOf :: (Ord v, Ord s) => Norm v s -> Norm v s
eyeOf (N conf integ) = N (mergeJNormJoin conf (wrapVars integ)) (J [M [B]]) 
  where
    wrapVars (J ms) = J (map wrapVars' ms)
    wrapVars' (M bs) = M (map wrapVars'' bs)
    wrapVars'' (V v) = VarEye v 
    wrapVars'' (VarVoice v) = (V v) 
    wrapVars'' (VarEye v) = VarEye v 
    wrapVars'' (UVoice s) = U s
    wrapVars'' (UEye   s) = UEye s
    wrapVars'' p = p
    
measure_jnorm :: forall v s. Int -> JNorm v s -> Int
measure_jnorm max (J [M [B]]) = max * max
measure_jnorm max (J [M []])  = max * max
measure_jnorm max (J [M [T]]) = 0
measure_jnorm max (J ms) = let num_conjuncts = len 0 ms in
                                  let unnamed_prins = num_conjuncts - max in
                                   (unnamed_prins * unnamed_prins) +
                                    (sum $ map (\(M bs) -> max - (len 0 (bs::[Base v s]))) ms)
  where
        len :: Num n => n -> [a] -> n
        len n [] = n
        len n (x:xs) = len (n+1) xs
                                      
joinWith :: (Ord v, Ord s) => JNorm v s -> JNorm v s -> Maybe (JNorm v s)
joinWith q bnd = let new_bnd = mergeJNormJoin bnd q
                 in if new_bnd == bnd then
                       Nothing
                     else
                       Just new_bnd

-- | Convert a 'SOP' term back to a TypePrin
reifyNorm :: (Ord v, Ord s) => Norm v s -> TypePrin v s
reifyNorm (N cp ip) = PT_Conj (reifyJNorm cp) (reifyJNorm ip)

reifyJNorm :: (Ord v, Ord s) => JNorm v s -> TypePrin v s
reifyJNorm (J [])     = PT_Bot 
reifyJNorm (J [p])    = reifyMNorm p
reifyJNorm (J (p:ps)) = let es = reifyJNorm (J ps) in
                          PT_Conj (reifyMNorm p) es

reifyMNorm :: (Ord v, Ord s) => MNorm v s -> TypePrin v s
reifyMNorm (M [])     = PT_Bot 
reifyMNorm (M [p])    = reifyBase p
reifyMNorm (M (p:ps)) = let es = reifyMNorm (M ps) in
                          PT_Disj (reifyBase p) es

reifyBase :: (Ord v, Ord s) => Base v s -> TypePrin v s
reifyBase (V v)   = PT_Var v
reifyBase (VarEye v)   = PT_Eye (PT_Var v)
reifyBase (VarVoice v)   = PT_Voice (PT_Var v)
reifyBase (U s)   = PT_Uninterp s
reifyBase (UEye s)   = PT_Eye (PT_Uninterp s)
reifyBase (UVoice s) = PT_Voice (PT_Uninterp s)
reifyBase (P s)   = PT_Name s
reifyBase B       = PT_Bot
reifyBase T       = PT_Top

{-
cartProd :: JNorm v s -> [JNorm v s]
cartProd (J ms) = [J $ map mkM ps | ps <- sequence [bs | (M bs) <- ms]]
  where mkM p = M [p]

flattenDelegations :: [(Norm v s, Norm v s)]
                   -> ([(JNorm v s, JNorm v s)], [(JNorm v s, JNorm v s)])
flattenDelegations givens = foldl
                      (\(cacc, iacc) given ->
                        case given of
                          -- convert to "base form"
                          -- base form is:
                          --  (b ∧ b ...) ≽ (b ∨ b ...)
                          --   joins of base principals on LHS
                          --   meets of base principals on RHS
                          (N supJC supJI, N (J infMCs) (J infMIs)) -> 
                            ([(supC, J [infC]) | supC <- cartProd supJC, infC <- infMCs] ++ cacc,
                             [(supI, (J [infI])) | supI <- cartProd supJI, infI <- infMIs] ++ iacc)
                      )
                      ([] :: [(JNorm v s, JNorm v s)], [] :: [(JNorm v s, JNorm v s)])
                      givens
  where
    cartProd (J ms) = [J $ map mkM ps | ps <- sequence [bs | (M bs) <- ms]]
    mkM p = M [p]
 {- 
   TODO: delegations based on structural edges
   - for each conjunction on the LHS, add a pseudo-node to the graph that is
       reachable from each conjunct and from which the intersection of the
       superiors of each conjunct are reachable.
   - for each disjunction on the RHS, add a pseudo-node to the graph that
       reaches the disjunction and is reachable from the intersection of
       the inferiors of each disjunct.
   - compute fixpoint
 -}

type DelClosure v s = [(JNorm v s, [JNorm v s])]
computeDelClosure :: forall v s. (Ord v, Ord s) => [(JNorm v s, JNorm v s)] -> DelClosure v s
computeDelClosure givens = -- pprTrace "computing closure from" (ppr givens) $
  [(inferior, superiors) | (inferior, _, superiors) <- closure initialEdges]
  where
    top = (J [M [T]])
    bot = (J [M [B]])
    baseSeqToJ seq = J [M seq]
    
    structJoinEdges :: JNorm v s -> [(JNorm v s, JNorm v s, [JNorm v s])]
    structJoinEdges (J []) = [] 
    structJoinEdges (J seq) = 
      {- for sequence of elements in each conjunct, add an edge from that sequence to the conjunct -}
      [(J inf, J inf, [J seq]) | inf <- subsequencesOfSize (length seq - 1) seq]
      {- recurse on all subsequences -}
      ++ concat [structJoinEdges (J inf) | inf <- subsequencesOfSize (length seq - 1) seq]

    structMeetEdges :: JNorm v s -> [(JNorm v s, JNorm v s, [JNorm v s])]
    structMeetEdges (J [M []]) = [] 
    structMeetEdges (J [M seq]) = 
      {- for each disjunct, add an edge to each subsequence of the disjunct -}
      [(baseSeqToJ seq, baseSeqToJ seq, map baseSeqToJ $ subsequencesOfSize (length seq - 1) seq)]
      ++ concat [structMeetEdges (J [M sup]) | sup <- subsequencesOfSize (length seq - 1) seq]
    {- for principals in base form, there are no other structural meet edges -}
    structMeetEdges (J seq) = []

    initialEdges :: [(JNorm v s, JNorm v s, [JNorm v s])]
    initialEdges = [(inf, inf, sort $ union (union (nub [gsup | (gsup, ginf) <- givens, ginf == inf])
                                            $ concat [jsups | (jinf, _, jsups) <- structJoinEdges inf, jinf == inf])
                                     $ (concat [msups | (minf, _, msups) <- structMeetEdges inf, minf == inf] ++ [top])
                                     )
                    | inf <- principals]

    {-
      For principals in a given in base form, 
        (b ∧ b ...) ≽ (b ∨ b ...)
      we want a node for each subsequence of conjuncts and disjuncts
    -}
    principals :: [JNorm v s]
    principals = [top, bot] ++ (nub $ concat [(map J $ concat [subsequencesOfSize i psC | i <- [1..length psC]]) ++
                                              (map baseSeqToJ $ concat [subsequencesOfSize i qs | i <- [1..length qs]])
                                             | (J psC, J [M qs]) <- givens])
    -- http://stackoverflow.com/questions/21265454/subsequences-of-length-n-from-list-performance
    subsequencesOfSize :: Int -> [a] -> [[a]]
    subsequencesOfSize n xs = let l = length xs
                              in if n>l then [] else subsequencesBySize xs !! (l-n)
    subsequencesBySize [] = [[[]]]
    subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                              in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

    closure edges = undefined
    closure edges = let (graph, vtxToEdges, prinToVtx) = graphFromEdges edges in
                     let vtxToPrin v = let (x, _, _) = vtxToEdges v in x in
                     [(vtxToPrin inf, vtxToPrin inf, 
                       (sort (map vtxToPrin $ reachable graph inf)))
                      | inf <- vertices graph]
                      -}
{-
prinType :: FlameRec -> s -> TypePrin v s
prinType flrec ty
  | Just ty1 <- coreView ty = prinType flrec ty1
prinType flrec (TyVarTy v) = PT_Var v
prinType flrec (TyConApp tc [])
  | tc == (ktop flrec) = PT_Top
  | tc == (kbot flrec) = PT_Bot
prinType flrec (TyConApp tc [x])
  | tc == (kname flrec)  = PT_Name x
  | tc == (kconf flrec)  = PT_Conf x
  | tc == (kinteg flrec) = PT_Integ x
  | tc == (kvoice flrec) = PT_Voice x
  | tc == (keye flrec)   = PT_Eye x
prinType flrec (TyConApp tc [x,y])
  | tc == (kconj flrec) = PT_Conj x y
  | tc == (kdisj flrec) = PT_Disj x y
prinType flrec ty = PT_Uninterp ty
-}
