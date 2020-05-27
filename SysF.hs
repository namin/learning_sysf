{-|
SysF.hs
=========
Will define syntax for System F, what terms and types look like. Follows
the specification in Chapter 23 of Pierce's Types and Programming Languages.
-}

{-|
TODO:
Typing, Evaluation
-}


{- ====================== Syntax of Terms & Types  ===========================-}
type Id = String

data Term = TmUnit
          | TmTrue
          | TmFalse
          | TmVar Id
          | TmAbs Id Type Term
          | TmApp Term Term
          | TmUniAbs Id Term
          | TmUniApp Term Type
          deriving (Eq)

-- For pretty printing terms
instance Show Term where
  show (TmUnit) = "(unit)"
  show (TmTrue) = "(true)"
  show (TmFalse) = "(false)"
  show (TmVar i) = id i
  show (TmAbs i typ trm) = concat ["(", "lam ", i, ":", "(", show typ, ").",
                                   show trm, ")"]
  show (TmApp trm1 trm2) = show trm1 ++ show trm2
  show (TmUniAbs i trm) = concat ["(", "forall ", i, ".", show trm, ")"]
  show (TmUniApp trm typ) = show trm ++ show typ

data Type = TyUnit
          | TyBool
          | TyVar Id
          | TyAbs Type Type
          | TyUni Type Type
          deriving (Eq)

-- For pretty printing types
instance Show Type where
  show (TyUnit) = "Unit"
  show (TyBool) = "Bool"
  show (TyVar i) = id i
  show (TyAbs typ1 typ2) = concat ["(", show typ1, " -> ", show typ2, ")"]
  show (TyUni typ1 typ2) = concat ["(", show typ1, ".", show typ2, ")"]


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
             | ErUniApp1 Term Type
             | ErUniApp2 Type
             deriving (Eq)

-- For pretty printing errors
instance Show TCError where
  show (ErVar x) = concat ["Variable ", x, " has no binding in the context."]
  show (ErTyVar x) = concat ["Type variable ", x, " has no type."]
  show (ErApp1 trm1 trm2) = concat [show trm2, " is not a valid input to ",
                                   show trm1, "."]
  show (ErApp2 trm) = concat [show trm, " must be an abstraction."]
  show (ErUniApp1 trm typ) = concat [show typ, "is not a valid input to ",
                                    show trm, "."]
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
  where ctx' = filter (\x -> idFromBinding x == i) ctx

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
