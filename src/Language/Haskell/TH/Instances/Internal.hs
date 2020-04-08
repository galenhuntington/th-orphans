{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Defines a utility function for deriving 'Quasi' instances for monad
-- transformer data types.
module Language.Haskell.TH.Instances.Internal
  ( deriveQuasiTrans
  , deriveQuoteTrans
  , Proxy2
  ) where

import qualified Control.Monad.Trans as MTL (lift)
import Language.Haskell.TH.Lib
import Language.Haskell.TH.Ppr (pprint)
import Language.Haskell.TH.Syntax hiding (newName)
#if MIN_VERSION_template_haskell(2,17,0)
import Language.Haskell.TH.Syntax (newName)
#else
import Language.Haskell.TH.Syntax.Compat (Quote(newName))
#endif

deriveQuasiTrans ::
     Q Type  -- ^ The instance head. For example, this might be of the form:
             --
             --   > [t| forall r m. Quasi m => Proxy2 (ReaderT r m) |]
             --
             --   Why use 'Proxy2' instead of 'Quasi'? Sadly, GHC 7.0/7.2 will
             --   not accept it if you use the latter due to old TH bugs, so we
             --   use 'Proxy2' as an ugly workaround.
  -> Q Exp   -- ^ The implementation of 'qRecover'
  -> Q [Dec] -- ^ The 'Quasi' instance declaration
deriveQuasiTrans qInstHead qRecoverExpr = deriveTrans ''Quasi qInstHead qInstMethDecs
  where
    qInstMethDecs :: [Q Dec]
    qInstMethDecs =
      let instMeths :: [(Name, Q Exp)]
          instMeths =
            [ -- qRecover is different for each instance
              ('qRecover,            qRecoverExpr)

              -- The remaining methods are straightforward
            , ('qNewName,            [| MTL.lift . qNewName |])
            , ('qReport,             [| \a b -> MTL.lift $ qReport a b |])
            , ('qReify,              [| MTL.lift . qReify |])
            , ('qLocation,           [| MTL.lift qLocation |])
            , ('qRunIO,              [| MTL.lift . qRunIO |])
#if MIN_VERSION_template_haskell(2,7,0)
            , ('qReifyInstances,     [| \a b -> MTL.lift $ qReifyInstances a b |])
            , ('qLookupName,         [| \a b -> MTL.lift $ qLookupName a b |])
            , ('qAddDependentFile,   [| MTL.lift . qAddDependentFile |])
# if MIN_VERSION_template_haskell(2,9,0)
            , ('qReifyRoles,         [| MTL.lift . qReifyRoles |])
            , ('qReifyAnnotations,   [| MTL.lift . qReifyAnnotations |])
            , ('qReifyModule,        [| MTL.lift . qReifyModule |])
            , ('qAddTopDecls,        [| MTL.lift . qAddTopDecls |])
            , ('qAddModFinalizer,    [| MTL.lift . qAddModFinalizer |])
            , ('qGetQ,               [| MTL.lift qGetQ |])
            , ('qPutQ,               [| MTL.lift . qPutQ |])
# endif
# if MIN_VERSION_template_haskell(2,11,0)
            , ('qReifyFixity,        [| MTL.lift . qReifyFixity |])
            , ('qReifyConStrictness, [| MTL.lift . qReifyConStrictness |])
            , ('qIsExtEnabled,       [| MTL.lift . qIsExtEnabled |])
            , ('qExtsEnabled,        [| MTL.lift qExtsEnabled |])
# endif
#elif MIN_VERSION_template_haskell(2,5,0)
            , ('qClassInstances,     [| \a b -> MTL.lift $ qClassInstances a b |])
#endif
#if MIN_VERSION_template_haskell(2,14,0)
            , ('qAddForeignFilePath, [| \a b -> MTL.lift $ qAddForeignFilePath a b |])
            , ('qAddTempFile,        [| MTL.lift . qAddTempFile |])
#elif MIN_VERSION_template_haskell(2,12,0)
            , ('qAddForeignFile,     [| \a b -> MTL.lift $ qAddForeignFile a b |])
#endif
#if MIN_VERSION_template_haskell(2,13,0)
            , ('qAddCorePlugin,      [| MTL.lift . qAddCorePlugin |])
#endif
#if MIN_VERSION_template_haskell(2,16,0)
            , ('qReifyType,          [| MTL.lift . qReifyType |])
#endif
            ]

          mkDec :: Name -> Q Exp -> Q Dec
          mkDec methName methRhs = valD (varP methName) (normalB methRhs) []

      in map (uncurry mkDec) instMeths

deriveQuoteTrans ::
     Q Type  -- ^ The instance head. For example, this might be of the form:
             --
             --   > [t| forall r m. Quote m => Proxy2 (ReaderT r m) |]
             --
             --   Why use 'Proxy2' instead of 'Quote'? Sadly, GHC 7.0/7.2 will
             --   not accept it if you use the latter due to old TH bugs, so we
             --   use 'Proxy2' as an ugly workaround.
  -> Q [Dec] -- ^ The 'Quasi' instance declaration
deriveQuoteTrans qInstHead = deriveTrans ''Quote qInstHead qInstMethDecs
  where
    qInstMethDecs :: [Q Dec]
    qInstMethDecs = [valD (varP 'newName) (normalB [| MTL.lift . newName |]) []]

deriveTrans ::
     Name    -- ^ The class to derive
  -> Q Type  -- ^ The instance head
  -> [Q Dec] -- ^ The implementations of each method in the instance
  -> Q [Dec] -- ^ The derived instance declaration
deriveTrans clsName qInstHead qInstMethDecs = do
  instHead <- qInstHead
  let (instCxt, mangledInstTy) = decomposeType instHead
      qInstCxt = return instCxt
      qInstTy  = case mangledInstTy of
                   ConT proxy2 `AppT` instTy
                     |  proxy2 == ''Proxy2
                     -> conT clsName `appT` return instTy
                   _ -> fail $ "Unexpected type " ++ pprint mangledInstTy
  instDec <- instanceD qInstCxt qInstTy qInstMethDecs
  return [instDec]
  where
    decomposeType :: Type -> (Cxt, Type)
    decomposeType (ForallT _tvbs ctxt ty) = (ctxt, ty)
    decomposeType ty                      = ([],   ty)

-- | See the Haddocks for 'deriveQuasiTrans' for an explanation of why this
-- type needs to exist.
data Proxy2 (m :: * -> *)
