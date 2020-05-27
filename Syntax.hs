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

type Id = String

data Term = TmVar Id
          | TmAbs Id Type Term
          | TmApp Term Term
          | TmUniAbs Id Term
          | TmUniApp Term Type
          deriving (Eq)

-- For pretty printing terms
instance Show Term where
  show (TmVar i) = id i
  show (TmAbs i typ trm) = foldr1 (\x a -> x ++ a) strings
    where strings = ["(", "lam ", i, ":", "(", show typ, ").", show trm, ")"]
  show (TmApp trm1 trm2) = show trm1 ++ show trm2
  show (TmUniAbs i trm) = foldr1 (\x a -> x ++ a) strings
    where strings = ["(", "forall ", i, ".", show trm, ")"]
  show (TmUniApp trm typ) = show trm ++ show typ

data Type = TyVar Id
          | TyAbs Type Type
          | TyUni Type Type
          deriving (Eq)

-- For pretty printing types
instance Show Type where
  show (TyVar i) = id i
  show (TyAbs typ1 typ2) = foldr1 (\x a -> x ++ a) strings
    where strings = ["(", show typ1, " -> ", show typ2, ")"]
  show (TyUni typ1 typ2) = foldr1 (\x a -> x ++ a) strings
    where strings = ["(", show typ1, ".", show typ2, ")"]

data Binding = TmBind Id Term
             | TyBind Id Type
             deriving (Eq)

type Context = [Binding]

-- typeOf :: Term -> Context -> Either

fo :: Int -> Either Bool Int
fo 0 = Left True
fo x = Right x

foo :: Int -> Either Bool Int
foo x = do
  y <- fo x
  return y
