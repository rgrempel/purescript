-- |
-- Inlining Typeable instances
--
module Language.PureScript.TypeChecker.Typeable where

import Prelude.Compat

import Control.Monad.Error.Class (MonadError(..))
import Control.Monad.State
import Control.Monad.Writer

import Language.PureScript.AST
import Language.PureScript.Crash
import Language.PureScript.Errors
import Language.PureScript.Names
import Language.PureScript.TypeChecker.Monad
import Language.PureScript.TypeClassDictionaries
import Language.PureScript.Types
import Language.PureScript.Kinds (Kind(..))
import Language.PureScript.TypeChecker.Kinds (kindOf)

import Debug.Trace


canInlineTypeable :: Type -> Bool
canInlineTypeable = everythingOnTypes (&&) canInline
  where
    -- Make sure we have a module name
    canInline (TypeConstructor (Qualified (Just _) _)) = True
    canInline TypeLevelString{} = True
    canInline TypeApp{} = True
    canInline REmpty{} = True
    canInline RCons{} = True
    canInline KindedType{} = True
    canInline _ = False


inlineTypeable
  :: forall m. (MonadError MultipleErrors m, MonadState CheckState m, MonadWriter MultipleErrors m)
  => Qualified (ProperName 'ClassName)
  -> [Type]
  -> m (Maybe TypeClassDictionaryInScope)
inlineTypeable cn (ty : _) | cn == typeableClassName && canInlineTypeable ty = do
  kindable <- kindableFor <$> kindOf ty
  typeable <- typeRepTypeFor ty
  return $ Just $ TypeClassDictionaryInScope
    (Qualified Nothing (Ident ""))
    []
    typeableClassName
    [ty, typeable, kindable]
    Nothing
inlineTypeable _ _ = return Nothing


-- |
-- The qualified name for Type.Typeable.Typeable, which is a constraint that the
-- compiler treats specially, inlining instances on the fly when requested.
-- This means that you don't have to define your own `Typeable` instances (or
-- even derive them), which is sensible, because the compiler already
-- knows everything needed to make an instance when one is wanted.
--
-- An alternative would be to make `Typeable` a primitive class name, like `Partial`.
--
typeableClassName :: Qualified (ProperName 'ClassName)
typeableClassName = mkQualified (ProperName "Typeable") typeableModule

typeableModule :: ModuleName
typeableModule = moduleNameFromString "Type.Typeable"

mkConstructor :: String -> Type
mkConstructor s = TypeConstructor $ mkQualified (ProperName s) typeableModule

typeRepSymbol :: Type
typeRepSymbol = mkConstructor "TypeSymbol"

typeRepRow :: Type -> Type
typeRepRow = TypeApp (mkConstructor "TypeRow")

typeRepTypeLiteral :: Type -> Type
typeRepTypeLiteral = TypeApp (mkConstructor "TypeLiteral")

typeRepTypeApp :: Type -> Type -> Type
typeRepTypeApp = TypeApp . TypeApp (mkConstructor "TypeApp") 

kindableStar :: Type
kindableStar = mkConstructor "KindStar"

kindableEffect :: Type
kindableEffect = mkConstructor "KindEffect"

kindableSymbol :: Type
kindableSymbol = mkConstructor "KindSymbol"

kindableArrow :: Type -> Type -> Type
kindableArrow = TypeApp . TypeApp (mkConstructor "KindArrow")

kindableRow :: Type -> Type
kindableRow = TypeApp (mkConstructor "KindRow")


kindableFor :: Kind -> Type
kindableFor (KUnknown _) = internalError "Kinds should be inferred by now."
kindableFor Star = kindableStar
kindableFor Bang = kindableEffect
kindableFor (Row r) = kindableRow (kindableFor r)
kindableFor (FunKind arg result) = kindableArrow (kindableFor arg) (kindableFor result)
kindableFor Symbol = kindableSymbol


typeRepTypeFor
  :: forall m. (MonadError MultipleErrors m, MonadState CheckState m, MonadWriter MultipleErrors m)
  => Type
  -> m Type
typeRepTypeFor ty =
  case ty of 
    TypeLevelString _ ->
      return typeRepSymbol

    TypeApp a b -> do
      typeForA <- typeRepTypeFor a
      typeForB <- typeRepTypeFor b
      return $ typeRepTypeApp typeForA typeForB

    TypeConstructor _ -> do
      kind <- kindOf ty
      return $ typeRepTypeLiteral (kindableFor kind)

    KindedType t _ ->
      typeRepTypeFor t

    _ ->
      internalError $ "Attempting to inline a `TypeRep` for a type that should not be reachable here: " <> show ty


typeRepFunction
  :: forall m. (MonadError MultipleErrors m, MonadState CheckState m, MonadWriter MultipleErrors m)
  => Type
  -> m Expr
typeRepFunction ty = do
  tyLit <- typeRepLiteral ty
  pure $ Abs (Right NullBinder) tyLit

-- Construct a literal representation for the type `a` when inlining a
-- `Typeable a` dictionary.
--
-- Because we're inlining these where demanded, it is convenient to represent
-- them using only primitive types. Otherwise, we'd have to arrange to bring
-- the relevant ADT into scope on-demand, which seems awkward.
--
-- So, this generates a literal which is essentially a `Foreign` in Purescript
-- terms. Since this is literally inserted into the source, and may be done so
-- many times, the form of the literal is very compact. Basically, each `TypeRep`
-- is a primitive array, where the first value is an integer, representing
-- what might normally be a data constructor, and the remaining values are the
-- arguments which that data constructor would normally take.
--
-- We leave off the KindRep information in cases where it can be inferred from
-- the type.
typeRepLiteral
  :: forall m. (MonadError MultipleErrors m, MonadState CheckState m, MonadWriter MultipleErrors m)
  => Type
  -> m Expr
typeRepLiteral ty =
  case ty of
    TypeLevelString s ->
      return $ string s

    -- Note that we don't match if the module name is unspecified
    TypeConstructor (Qualified (Just tyConModule) tyConName) ->
      return $ object
        [ ("m", string (runModuleName tyConModule))
        , ("t", string (runProperName tyConName))
        ]

    TypeApp tyFunc tyArg -> do
      tf <- typeRepLiteral tyFunc
      ta <- typeRepLiteral tyArg
      return $ object
        [ ("a", tf)
        , ("p", ta)
        ]

{-
    -- For rows, we need to explicitly give the kind information, since
    -- we wouldn't be able to infer it in the case of empty rows.
    REmpty -> do
      return $ ctor 3
        [ object []
        , kindRepLiteral kind
        ]

    RCons{} -> do
      kind <- kindOf ty
      rows <- accumRows ty []
      return $ ctor 3
        [ object rows
        , kindRepLiteral kind
        ]
-}

    KindedType t _ ->
      typeRepLiteral t

    _ ->
        internalError $ "Attempting to inline a `TypeRepT` for a type that should not be reachable here: " <> show ty

  where
    -- Recurse into the supplied type, using the supplied accumulator
    -- to accumulate `RCons` values, so long as we keep finding them.
    accumRows :: Type -> [(String, Expr)] -> m [(String, Expr)]
    accumRows (RCons label t t') acc = do
      row <- typeRepLiteral t
      accumRows t' ((label, row) : acc)
    accumRows _ acc = return acc

    string :: String -> Expr
    string = Literal . StringLiteral

    integer :: Integer -> Expr
    integer = Literal . NumericLiteral . Left

    object :: [(String, Expr)] -> Expr
    object = Literal . ObjectLiteral

    array :: [Expr] -> Expr
    array = Literal . ArrayLiteral

