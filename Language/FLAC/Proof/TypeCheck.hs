{-# LANGUAGE GADTs, DataKinds, PolyKinds, RankNTypes #-}

module Language.FLAC.Proof.TypeCheck where

import Data.Singletons.Prelude
import Data.Singletons.Decide
import Data.Text (Text)

import qualified Language.FLAC.Syntax.Runtime as R
import qualified Language.FLAC.Syntax.Promoted as P
import Language.FLAC.Syntax
import Language.FLAC.Proof

type TyCtx = [(Text, R.Type)]
type DelCtx = [(R.Prin, R.Prin)]

with2Sing :: forall ka kb r.
             (SingKind ka, SingKind kb)
             => Demote ka -> Demote kb
             -> (forall (a :: ka) (b :: kb).
                  Sing a -> Sing b -> r)
             -> r
with2Sing a b f = withSomeSing a (\sa ->
                       withSomeSing b (\sb -> f sa sb))

with3Sing :: forall ka kb kc r.
             (SingKind ka, SingKind kb, SingKind kc)
             => Demote ka -> Demote kb -> Demote kc
             -> (forall (a :: ka) (b :: kb) (c :: kc).
                  Sing a -> Sing b -> Sing c -> r)
             -> r
with3Sing a b c f = withSomeSing a (\sa ->
                       withSomeSing b (\sb ->
                         withSomeSing c (\sc -> f sa sb sc)))

prove :: R.Exp -> DelCtx -> TyCtx -> R.Prin -> Maybe SFLAC
prove e_ dx_ tx_ p_ = with3Sing dx_ tx_ p_ (go e_)
  where
    go :: forall (a :: [(P.Prin, P.Prin)]) (b :: [(Symbol, P.Type)]) (c :: P.Prin) .
          R.Exp -> Sing a -> Sing b -> Sing c -> Maybe SFLAC
    go R.EUnit sdx stx sp = Just $ SFLAC sdx stx sp SUnit EUnit
    go (R.Var x) sdx stx sp = withSomeSing x $
      \sx -> case sLookup sx stx of
        SJust st -> Just $ SFLAC sdx stx sp st (Var sx)
        _ -> Nothing
    go (R.EActsFor a b) sdx stx sp = with2Sing a b $
      \sa sb -> Just $ SFLAC sdx stx sp (SActsFor sa sb) (Del sa sb)
    go (R.App e1 e2) sdx stx sp = case (prove e1 dx_ tx_ p_, prove e2 dx_ tx_ p_) of
      (Just (SFLAC sdx'  stx'  sp' (SFn st1 spc' st2) f1),
       Just (SFLAC sdx'' stx'' sp'' st1' f2)) ->
        case (sdx %~ sdx', sdx' %~ sdx'', stx %~ stx', stx' %~ stx'',
              sp %~ sp', sp' %~ sp'', st1 %~ st1',
              sDelegates sdx (SConf spc') (SConf sp) %~ STrue,
              sDelegates sdx (SInteg sp) (SInteg spc') %~ STrue) of
          (Proved Refl, Proved Refl, Proved Refl, Proved Refl,
           Proved Refl, Proved Refl, Proved Refl, Proved Refl, Proved Refl) ->
            Just $ SFLAC sdx stx sp st2 (App f1 f2)
          _ -> Nothing
      _ -> Nothing
    go (R.Pair e1 e2) sdx stx sp = case (prove e1 dx_ tx_ p_, prove e2 dx_ tx_ p_) of
      (Just (SFLAC sdx'  stx'  sp'  st1 f1),
       Just (SFLAC sdx'' stx'' sp'' st2 f2)) ->
        case (sdx %~ sdx', sdx' %~ sdx'', stx %~ stx', stx' %~ stx'',
              sp %~ sp', sp' %~ sp'') of
          (Proved Refl, Proved Refl, Proved Refl, Proved Refl,
           Proved Refl, Proved Refl) ->
            Just $ SFLAC sdx stx sp (STimes st1 st2) (Pair f1 f2)
          _ -> Nothing
      _ -> Nothing
    go (R.Protect l e) sdx stx sp = case prove e dx_ tx_ p_ of
      Just (SFLAC sdx' stx' sp' st f) -> withSomeSing l $ \sl ->
        case (sdx %~ sdx', stx %~ stx', sp %~ sp',
              sDelegates sdx (SConf sl) (SConf sp) %~ STrue,
              sDelegates sdx (SInteg sp) (SInteg sl) %~ STrue
             ) of
          (Proved Refl, Proved Refl, Proved Refl, Proved Refl, Proved Refl) ->
            Just $ SFLAC sdx stx sp (SSays sl st) (UnitM sl f)
          _ -> Nothing
      _ -> Nothing
    go (R.TApp e1 t1) sdx stx sp = case prove e1 dx_ tx_ p_ of
      Just (SFLAC sdx' stx' sp' (SForall sx sp'' st) f) -> withSomeSing t1 $ \st1 ->
        case (sdx %~ sdx', stx %~ stx', sp %~ sp',
              sDelegates sdx (SConf sp'') (SConf sp) %~ STrue,
              sDelegates sdx (SInteg sp) (SInteg sp'') %~ STrue
             ) of
          (Proved Refl, Proved Refl, Proved Refl, Proved Refl, Proved Refl) ->
            Just $ SFLAC sdx stx sp (sSubst st sx st1) (TApp f st1)
          _ -> Nothing
      _ -> Nothing
    go (R.Project1 e) sdx stx sp = case prove e dx_ tx_ p_  of
      Just (SFLAC sdx' stx' sp' (STimes st1 _) f) ->
        case (sdx %~ sdx', stx %~ stx', sp %~ sp') of
          (Proved Refl, Proved Refl, Proved Refl) ->
            Just $ SFLAC sdx stx sp st1 (Project1 f)
          _ -> Nothing
      _ -> Nothing
    go (R.Project2 e) sdx stx sp = case prove e dx_ tx_ p_  of
      Just (SFLAC sdx' stx' sp' (STimes _ st2) f) ->
        case (sdx %~ sdx', stx %~ stx', sp %~ sp') of
          (Proved Refl, Proved Refl, Proved Refl) ->
            Just $ SFLAC sdx stx sp st2 (Project2 f)
          _ -> Nothing
      _ -> Nothing
    go (R.Inject1 e (Just t2)) sdx stx sp = withSomeSing t2 $ \st2 ->
      case prove e dx_ tx_ p_ of
        Just (SFLAC sdx' stx' sp' st1 f1) ->
          case (sdx %~ sdx', stx %~ stx', sp %~ sp') of
            (Proved Refl, Proved Refl, Proved Refl) ->
              Just $ SFLAC sdx stx sp (SPlus st1 st2) (Inject1 f1)
            _ -> Nothing
        _ -> Nothing
    go (R.Inject1 _ Nothing) _ _ _ = Nothing
    go (R.Inject2 e (Just t1)) sdx stx sp = withSomeSing t1 $ \st1 ->
      case prove e dx_ tx_ p_ of
        Just (SFLAC sdx' stx' sp' st2 f2) ->
          case (sdx %~ sdx', stx %~ stx', sp %~ sp') of
            (Proved Refl, Proved Refl, Proved Refl) ->
              Just $ SFLAC sdx stx sp (SPlus st1 st2) (Inject2 f2)
            _ -> Nothing
        _ -> Nothing
    go (R.Inject2 _ Nothing) _ _ _ = Nothing
    go (R.Case e x e1 y e2) sdx stx sp = case prove e dx_ tx_ p_ of
      Just (SFLAC sdx' stx' sp' (SPlus st1 st2) f) ->
        case (sdx %~ sdx', stx %~ stx', sp %~ sp') of
          (Proved Refl, Proved Refl, Proved Refl) -> with2Sing x y $ \sx sy ->
            let stx1 = SCons (STuple2 sx st1) stx
                stx2 = SCons (STuple2 sy st2) stx in
              case (prove e1 dx_ (fromSing stx1) p_, prove e2 dx_ (fromSing stx2) p_) of
                (Just (SFLAC sdx''  stx''  sp''  st  f1),
                 Just (SFLAC sdx''' stx''' sp''' st' f2)) ->
                  case (sdx %~ sdx'', sdx %~ sdx''', stx1 %~ stx'', stx2 %~ stx''',
                       sp %~ sp'', sp %~ sp''', st %~ st',
                       sDelegatesType sdx sp st %~ STrue) of
                    (Proved Refl, Proved Refl, Proved Refl, Proved Refl,
                     Proved Refl, Proved Refl, Proved Refl, Proved Refl) ->
                      Just $ SFLAC sdx stx sp st (Case f sx f1 sy f2)
                    _ -> Nothing
                _ -> Nothing
          _ -> Nothing
      _ -> Nothing
    go (R.Bind x e1 e2) sdx stx sp = case prove e1 dx_ tx_ p_ of
      Just (SFLAC sdx' stx' sp' (SSays sl st') f1) ->
        case (sdx %~ sdx', stx %~ stx', sp %~ sp') of
          (Proved Refl, Proved Refl, Proved Refl) -> withSomeSing x $ \sx ->
            let stx1 = SCons (STuple2 sx st') stx
                slub = sLub sp sl in
              case prove e2 dx_ (fromSing stx1) (fromSing slub) of
                Just (SFLAC sdx'' stx'' sp'' st'' f2) ->
                  case (sdx %~ sdx'', stx1 %~ stx'', slub %~ sp'',
                       sDelegatesType sdx slub st'' %~ STrue) of
                    (Proved Refl, Proved Refl, Proved Refl, Proved Refl) ->
                      Just $ SFLAC sdx stx sp st'' (Bind sx f1 f2)
                    _ -> Nothing
                _ -> Nothing
          _ -> Nothing
      _ -> Nothing
    go (R.Assume e1 e2) sdx stx sp = case prove e1 dx_ tx_ p_ of
      Just (SFLAC sdx' stx' sp' (SActsFor sa sb) f1) ->
        case (sdx %~ sdx', stx %~ stx', sp %~ sp') of
          (Proved Refl, Proved Refl, Proved Refl) ->
            let sdx'' = SCons (STuple2 sa sb) sdx
                dx'' = fromSing sdx'' in
              case prove e2 dx'' tx_ p_ of
                Just (SFLAC sdx''' stx''' sp''' st''' f2) ->
                  case (sdx'' %~ sdx''', stx %~ stx''', sp %~ sp''',
                       sDelegates sdx sp (SVoice sb) %~ STrue,
                       sDelegates sdx (SVoice (SConf sa)) (SVoice (SConf sb)) %~ STrue) of
                    (Proved Refl, Proved Refl, Proved Refl, Proved Refl, Proved Refl) ->
                      Just $ SFLAC sdx stx sp st''' (Assume f1 f2)
                    _ -> Nothing
                _ -> Nothing
          _ -> Nothing
      _ -> Nothing
    go (R.Lam x t pc' e) sdx stx sp = with3Sing x t pc' $ \sx st spc' ->
      case prove e dx_ tx_ pc' of
        Just (SFLAC sdx' stx' spc'' st2 f) ->
          case (sLookup sx stx %~ SJust st, sdx %~ sdx', stx %~ stx', spc' %~ spc'') of
            (Proved Refl, Proved Refl, Proved Refl, Proved Refl) ->
              Just $ SFLAC sdx (sRemove sx stx) sp (SFn st spc' st2) (Lambda sx st spc' f)
            _ -> Nothing
        _ -> Nothing
    go (R.LAM x pc' e) sdx stx sp = with2Sing x pc' $ \sx spc' ->
      case prove e dx_ tx_ pc' of
        Just (SFLAC sdx' stx' spc'' st f) ->
          case (sdx %~ sdx', stx %~ stx', spc' %~ spc'', sLookup sx stx %~ SNothing) of
            (Proved Refl, Proved Refl, Proved Refl, Proved Refl) ->
              Just $ SFLAC sdx stx sp (SForall sx spc' st) (TLambda sx spc' f)
            _ -> Nothing
        _ -> Nothing
