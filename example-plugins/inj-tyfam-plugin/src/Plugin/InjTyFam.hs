{-# LANGUAGE RecordWildCards #-}

module Plugin.InjTyFam (
  plugin,
  tcPlugin,
  ) where

-- base
import           Data.Maybe (fromMaybe)

-- ghc
import qualified GHC.Core
  as GHC
    ( Expr(..) )
import qualified GHC.Core.Coercion
  as GHC
    ( Coercion
    , mkPrimEqPredRole, mkUnivCo
    )
import qualified GHC.Core.Predicate
  as GHC
    ( Pred(..), classifyPredType
    , EqRel(..)
    )
import qualified GHC.Core.TyCo.Rep
  as GHC
    ( UnivCoProvenance(..) )
import qualified GHC.Core.Type
  as GHC
    ( getTyVar_maybe, mkTyConApp, splitTyConApp_maybe )
import qualified GHC.Plugins
  as GHC
    ( Plugin(..), defaultPlugin, purePlugin )
import qualified GHC.Core.TyCon
  as GHC
    ( TyCon(..)
    , Injectivity(..), tyConInjectivityInfo
    )
import qualified GHC.Core.Unify
  as GHC
    ( tcMatchTy )
import qualified GHC.Tc.Plugin
  as GHC
    ( newGiven )
import qualified GHC.Tc.Types
  as GHC
    ( TcPlugin(..)
    , TcPluginM
    , TcPluginResult(..)
    )
import qualified GHC.Tc.Types.Constraint
  as GHC
    ( Ct(..), ctPred, ctLoc, ctEvTerm
    , Xi
    , bumpCtLocDepth, mkNonCanonical
    )
import qualified GHC.Tc.Types.Evidence
  as GHC
    ( EvTerm, Role(..) )
import qualified GHC.Tc.Utils.TcType
  as GHC
    ( TcType )
import qualified GHC.Types.Var.Env
  as GHC
    ( VarEnv
    , lookupVarEnv, mkVarEnv
    )

--------------------------------------------------------------------------------


-- | Just 'tcPlugin', with 'GHC.purePlugin' set

plugin :: GHC.Plugin
plugin = GHC.defaultPlugin
    {
      GHC.pluginRecompile = GHC.purePlugin
    ,
      GHC.tcPlugin = \_opts -> pure tcPlugin
    }

-- | A typechecker plugin that decomposes Given equalities headed by
-- an injective type family,
-- <https://downloads.haskell.org/ghc/8.6.5/docs/html/users_guide/glasgow_exts.html#injective-type-families>
--
-- The plugin user is " opting in " to
-- <https://gitlab.haskell.org/ghc/ghc/issues/10833>

tcPlugin :: GHC.TcPlugin
tcPlugin = GHC.TcPlugin
    {
      GHC.tcPluginInit = pure ()
    ,
      GHC.tcPluginSolve = \() gs ds ws -> do
        let
          fskEnv :: FskEnv
          fskEnv = mkFskEnv gs

        (uncurry GHC.TcPluginOk . mconcat) <$>
          if null ds && null ws
          then mapM (simplifyG fskEnv) gs   -- we handle G-mode
          else pure []   -- GHC already handles W-mode
    ,
      GHC.tcPluginStop = \() -> pure ()
    }

-----

type M = GHC.TcPluginM

-- | The arguments to 'TcRnTypes.TcPluginOk'

type Ok = ([(GHC.EvTerm, GHC.Ct)], [GHC.Ct])

-- | See 'tcPlugin'

simplifyG :: FskEnv -> GHC.Ct -> M Ok
simplifyG fskEnv ct =
    case ctPredicate of
      GHC.ClassPred{}  -> giveup   -- TODO don't need to unpack SCs, right?
      GHC.IrredPred{}  -> giveup
      GHC.ForAllPred{} -> giveup   -- TODO this is unreachable, right?
      GHC.EqPred eqRel lty rty -> case eqRel of
          GHC.ReprEq -> giveup   -- TODO anything useful to do here?
          GHC.NomEq  -> case (,) <$> prj lty <*> prj rty of
              Nothing ->
                  giveup   -- one side isn't an injective tyfam application
              Just ((ltc, ltys), (rtc, rtys)) ->
                  if ltc /= rtc then giveup else do
                    -- both sides apply the same tyfam

                    ( argUnifyCts, mbNewRhsTyFamArgs ) <- unifyInjArgs False [] [] ltys rtys
                    allNewCts <-
                      case mbNewRhsTyFamArgs of
                        Nothing ->
                          pure argUnifyCts
                        Just newRhsTyFamArgs -> do
                          let
                            rty' :: GHC.TcType
                            rty' = GHC.mkTyConApp rtc newRhsTyFamArgs
                          updatedOrigCt <- impliedGivenEq ct lty rty'
                          pure ( updatedOrigCt : argUnifyCts )

                    case allNewCts of
                      [] -> giveup
                      _  -> pure ([(ev, ct)], allNewCts)
  where
    ev :: GHC.EvTerm
    ev = GHC.ctEvTerm $ GHC.cc_ev ct

    prj :: GHC.TcType -> Maybe (GHC.TyCon, [TyFamArg])
    prj = splitInjTyFamApp_maybe . unfsk fskEnv

    giveup :: M Ok
    giveup = pure ([], [])

    ctPredicate :: GHC.Pred
    ctPredicate = GHC.classifyPredType (GHC.ctPred ct)

    unifyInjArgs :: Bool -> [GHC.TcType] -> [GHC.Ct] -> [TyFamArg] -> [TyFamArg] -> M ( [GHC.Ct], Maybe [GHC.TcType] )
    unifyInjArgs leftoversRemain newRhsTyFamArgs acc [] []
      | not ( null acc ) && leftoversRemain
      = pure ( acc, Just $ reverse newRhsTyFamArgs )
      | otherwise
      = pure ( acc, Nothing )
    unifyInjArgs leftoversRemain newRhsTyFamArgs acc (InjArg lty:ltys) (InjArg rty:rtys)
      | Just _ <- GHC.tcMatchTy lty rty
      = unifyInjArgs leftoversRemain (lty:newRhsTyFamArgs) acc ltys rtys
      | otherwise
      = do
        new <- impliedGivenEq ct lty rty
        unifyInjArgs leftoversRemain (lty:newRhsTyFamArgs) (new:acc) ltys rtys
    unifyInjArgs leftoversRemain newRhsTyFamArgs acc (NonInjArg lty:ltys) (NonInjArg rty:rtys)
      | Just _ <- GHC.tcMatchTy lty rty
      = unifyInjArgs leftoversRemain (rty:newRhsTyFamArgs) acc ltys rtys
      | otherwise
      = unifyInjArgs True (lty:newRhsTyFamArgs) acc ltys rtys
    unifyInjArgs _ _ _ _ _ = error "impossible!"

-- | Split an application of injective tycon into the tycon and its
-- arguments that have fundeps

data TyFamArg
  = InjArg    !GHC.TcType
  | NonInjArg !GHC.TcType

splitInjTyFamApp_maybe :: GHC.TcType -> Maybe (GHC.TyCon, [TyFamArg])
splitInjTyFamApp_maybe t = do
    (tc, args) <- GHC.splitTyConApp_maybe t
    case GHC.tyConInjectivityInfo tc of
        GHC.NotInjective -> Nothing
        GHC.Injective is -> Just (tc, [ if isInj then InjArg arg else NonInjArg arg | (isInj, arg) <- zip is args ])

-- | Emit a new Given equality constraint implied by another Given
-- equality constraint

impliedGivenEq :: GHC.Ct -> GHC.TcType -> GHC.TcType -> M GHC.Ct
impliedGivenEq ct lty rty = do
    let
      new_co :: GHC.Coercion
      new_co = GHC.mkUnivCo
        (GHC.PluginProv "inj-tyfam-plugin")
        GHC.Nominal
        lty
        rty

    -- TODO how to incorporate @ctEvId ct@? (see #15248 on GitLab ghc)
    new_ev <- GHC.newGiven
      (GHC.bumpCtLocDepth (GHC.ctLoc ct))  -- TODO don't bump?
      (GHC.mkPrimEqPredRole GHC.Nominal lty rty)
      (GHC.Coercion new_co)

    pure $ GHC.mkNonCanonical new_ev

-----

-- | See 'mkFskEnv'

type FskEnv = GHC.VarEnv (GHC.TyCon, [GHC.Xi])

-- | An incremental map from the @FunEq@s
--
-- NOTE not necessarily idempotent

mkFskEnv :: [GHC.Ct] -> FskEnv
mkFskEnv cts =
    GHC.mkVarEnv
    [ (cc_fsk, (cc_fun, cc_tyargs))
    | GHC.CFunEqCan{..} <- cts
    ]

unfsk :: FskEnv -> GHC.TcType -> GHC.TcType
unfsk fskEnv t = fromMaybe t $ do
    v <- GHC.getTyVar_maybe t
    uncurry GHC.mkTyConApp <$> GHC.lookupVarEnv fskEnv v
