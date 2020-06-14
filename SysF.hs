{-|
SysF.hs
=========
Defines syntax, typing, evaluation for System F. Follows the specification in
Chapter 23 of Pierce's Types and Programming Languages.
-}

module SysF where

import Data.Map as Map

{- ====================== Syntax of Terms & Types  ==========================-}
type Id = String

data Term = TmUnit
          | TmTrue
          | TmFalse
          | TmVar Id
          | TmAbs Id Type Term
          | TmApp Term Term
          | TmTAbs Id Term
          | TmTApp Term Type
          deriving (Eq)

-- For pretty printing terms
instance Show Term where
  show (TmUnit) = "unit"
  show (TmTrue) = "tt"
  show (TmFalse) = "ff"
  show (TmVar i) = id i
  show (TmAbs i typ trm) = concat ["(", "lam ", i, ":", "(", show typ, ").",
                                   show trm, ")"]
  show (TmApp trm1 trm2) = "(" ++ show trm1 ++ ")" ++ show trm2
  show (TmTAbs i trm) = concat ["(", "forall ", i, ".", show trm, ")"]
  show (TmTApp trm typ) = show trm ++ show typ

data Type = TyUnit
          | TyBool
          | TyVar Id
          | TyAbs Type Type
          | TyTAbs Id Type
          deriving (Eq)

-- For pretty printing types
instance Show Type where
  show (TyUnit) = "Unit"
  show (TyBool) = "Bool"
  show (TyVar i) = id i
  show (TyAbs typ1 typ2) = concat ["(", show typ1, " -> ", show typ2, ")"]
  show (TyTAbs i typ) = concat ["(", i, ".", show typ, ")"]


{- =============================== Typing  =================================-}
data Binding = TmBind Id Type
             | TyBind Id
             deriving (Eq, Show)

type Context = [Binding]

-- Different kinds of typechecking errors
data TCError = ErVar Id
             | ErTyVar Id
             | ErApp1 Term Term
             | ErApp2 Term
             | ErTApp Term
             deriving (Eq)

-- For pretty printing errors
instance Show TCError where
  show (ErVar x) = concat ["Variable ", x, " has no binding in the context."]
  show (ErTyVar x) = concat ["Type variable ", x, " has no type."]
  show (ErApp1 trm1 trm2) = concat [show trm2, " is not a valid input to ",
                                   show trm1, "."]
  show (ErApp2 trm) = concat [show trm, " must be an abstraction."]
  show (ErTApp trm) = concat [show trm, " must be a type abstraction."]

-- Extract id from a binding
idFromBinding :: Binding -> Id
idFromBinding (TmBind i _) = i
idFromBinding (TyBind i) = i

-- Extract a type, if applicable, from a binding
typeFromBinding :: Binding -> Either TCError Type
typeFromBinding (TmBind i typ) = Right typ
typeFromBinding (TyBind i) = Left $ ErTyVar i

-- Extract a type, if applicable, from a context
typeFromContext :: Id -> Context -> Either TCError Type
typeFromContext i [] = Left $ ErVar i
typeFromContext i ctx = case ctx' of
  [] -> Left (ErVar i)
  _ -> typeFromBinding (head ctx')
  where ctx' = Prelude.filter (\x -> idFromBinding x == i) ctx

-- Typecheck terms, with monadic error handling
typeCheck :: Term -> Context -> Either TCError Type
typeCheck (TmUnit) ctx = Right TyUnit
typeCheck (TmTrue) ctx = Right TyBool
typeCheck (TmFalse) ctx = Right TyBool
typeCheck (TmVar i) ctx = typeFromContext i ctx
typeCheck (TmAbs i typ trm) ctx = do
  typ' <- typeCheck trm ((TmBind i typ):ctx)
  return (TyAbs typ typ')
typeCheck (TmApp trm1 trm2) ctx = do
  typ1 <- typeCheck trm1 ctx
  typ2 <- typeCheck trm2 ctx
  case typ1 of
    (TyAbs typ11 typ12)
      | typ11 == typ2 -> Right $ typ12
      | otherwise -> Left $ ErApp1 trm1 trm2
    _ -> Left $ ErApp2 trm1
typeCheck (TmTAbs i trm) ctx = do
  typ <- typeCheck trm ((TyBind i):ctx)
  return (TyTAbs i typ)
typeCheck (TmTApp trm typ) ctx = do
  typ' <- typeCheck trm ctx
  case typ' of
    (TyTAbs i typ'') -> typeCheck (eval (TmTApp trm typ) (Map.empty, freshVars)) ctx
    otherwise -> Left $ ErTApp trm

{- =============================== Evaluation  =================================-}

-- Fresh variables for capture-avoiding substitution
freshVars :: [Id]
freshVars = genFresh (repeat "$x") [1..]

genFresh :: [Id] -> [Int] -> [Id]
genFresh (x:xs) (y:ys) = (x ++ (show y)) : genFresh xs ys


-- Environment holds term/type bindings + infinite list of fresh variables
type Env = (Map Id (Either Term Type), [Id])

subTerm :: Id -> Term -> Term -> Term
subTerm x s (TmUnit) = TmUnit
subTerm x s (TmTrue)= TmTrue
subTerm x s (TmFalse) = TmFalse
subTerm x s (TmVar i)
  | x == i    = s
  | otherwise = (TmVar i)



-- Evaluate terms, assuming well-typed
eval :: Term -> Env -> Term
eval (TmUnit) _ = TmUnit
eval (TmTrue) _ = TmTrue
eval (TmFalse) _ = TmFalse
eval (TmVar i) (m, _) = trm where (Left trm) = m ! i
eval (TmAbs i1 (TyVar i2) trm) (m, _) = TmAbs i1 typ trm where (Right typ) = m ! i2
eval (TmAbs i typ trm) env = TmAbs i typ trm
eval (TmApp (TmAbs i typ trm1) trm2) (m, fvs@(i':is))
  | Map.lookup i m == Nothing = eval trm1 (insert i (Left (eval trm2 (m,fvs))) m, fvs)
  | otherwise                 = eval trm1 (insert i' (Left (eval trm2 (m,is))) m, is)
eval (TmApp trm1 trm2) env =
  let trm1' = eval trm1 env
      trm2' = eval trm2 env
  in eval (TmApp trm1' trm2') env
eval (TmTApp (TmTAbs i trm) typ) (m, fvs@(i':is))
  | Map.lookup i m == Nothing = eval trm (insert i (Right typ) m, fvs)
  | otherwise                 = eval trm (insert i' (Right typ) m, is)
eval (TmTApp trm typ) env =
  let trm' = eval trm env
  in eval (TmTApp trm' typ) env

evalType :: Type -> Env -> Type
evalType (TyUnit) _ = TyUnit
evalType (TyBool) _ = TyBool
evalType (TyVar i) (m, _) = typ where (Right typ) = m ! i
evalType (TyAbs typ1 typ2) env =
  let typ1' = evalType typ1 env
      typ2' = evalType typ2 env
      in TyAbs typ1' typ2'
evalType (TyTAbs i typ) env = TyTAbs i (evalType typ env)

