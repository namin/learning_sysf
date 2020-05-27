{-|
SysF.hs
=========
Will define syntax for System F, what terms and types look like. Follows
the specification in Chapter 23 of Pierce's Types and Programming Languages.
-}

type Id = String

data Term = TmVar Id
          | TmAbs Id Type Term
          | TmApp Term Term
          | TmUniAbs Id Type Type
          | TmUniApp Type Type
          deriving (Eq)

data Type = TyVar Id
          | TyAbs Type Type
          | TyUni Id Type
          deriving (Eq)

data Binding = TmBind Id Term
             | TyBind Id Type
             deriving (Eq)

type Context = [Binding]

