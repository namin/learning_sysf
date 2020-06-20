{-|
Learning.hs
==============================================================================
Defines synthesis rules from types and examples. Follows the specification in
Chapter 3 and 4 of "Learning in System F".
-}

module Learning where

import SystemF
import qualified Data.Map as Map


{-========================= Generators from Type =============================-}

-- Calculates size of a type's AST
sizeType :: Type -> Int
sizeType (TyUnit) = 1
sizeType (TyBool) = 1
sizeType (TyVar _) = 1
sizeType (TyAbs typ1 typ2) = 1 + (sizeType typ1) + (sizeType typ2)
sizeType (TyTAbs _ typ) = 1 + (sizeType typ)

-- Generates all type variables
genTyVars :: Context -> [Type]
genTyVars ctx = [TyVar i | (TyBind i) <- ctx]

-- Generates all type abstractions to some AST depth n
genTyAbs :: Context -> Int -> [Type]
genTyAbs ctx n =
  let cartProd xs ys = [(x,y) | x <- xs, y <- ys]
      szs = [(n1, n - 1 - n1) | n1 <- [1..(n-1)]]
      typs = [(genITypes ctx (fst sz), genITypes ctx (snd sz)) | sz <- szs]
      abss = foldl (++) [] [cartProd ty1s ty2s | (ty1s, ty2s) <- typs]
      in [TyAbs typ1 typ2 | (typ1, typ2) <- abss]

-- Generates all universal type abstractions to some AST depth n
genTyTAbs :: Context -> Int -> [Type]
genTyTAbs _ 0 = []
genTyTAbs ctx n =
  let tyvs = [i | (TyBind i) <- ctx]
      typs = genITypes ctx (n-1)
      in [TyTAbs i typ | i <- tyvs, typ <- typs]

-- Generates all term variables at type
genTmVars :: Type -> Context -> [Term]
genTmVars typ ctx = [TmVar i | (TmBind i typ') <- ctx, typ' == typ]

-- Generates all term applications at type to some AST depth n
genTmApps :: Type -> Context -> Int -> [Term]
genTmApps typ12 ctx n =
  let cartProd xs ys = [(x,y) | x <- xs, y <- ys]
      szs = [(n1, n - 1 - n1) | n1 <- [1..(n-1)]]
      fTyps = [t | TmBind _ t@(TyAbs _ typ12') <- ctx, typ12' == typ12]
      fxs = [(genETerms typ ctx (fst sz), genITerms typ11' ctx (snd sz)) |
             typ@(TyAbs typ11' _) <- fTyps, sz <- szs]
      apps = foldl (++) [] [cartProd fs xs | (fs, xs) <- fxs]
      in [TmApp f x | (f,x) <- apps]

-- Generates all type applications at type to some AST depth n
genTmTApps :: Type -> Context -> Int -> [Term]
genTmTApps typ ctx n =
  let cartProd xs ys = [(x,y) | x <- xs, y <- ys]
      szs = [(n1, n - 1 - n1) | n1 <- [1..(n-1)]]
      fTyps = [t | TmBind i t@(TyTAbs i' typ') <- ctx]
      fxs = [(genETerms typf ctx (fst sz), genITypes ctx (snd sz)) |
             typf@(TyTAbs _ _) <- fTyps, sz <- szs]
      tapps = foldl (++) [] [cartProd fs xs | (fs, xs) <- fxs]
      in [TmTApp f x | (f,x) <- tapps,
                       typeCheck (TmTApp f x) ctx == Right typ]

-- Generates all elimination terms at type to some AST depth n
genETerms :: Type -> Context -> Int -> [Term]
genETerms _ _ 0 = []
genETerms (TyUnit) ctx 1 = genTmVars TyUnit ctx
genETerms (TyUnit) ctx n = (genTmApps TyUnit ctx n) ++
                           (genTmTApps TyUnit ctx n)
genETerms (TyBool) ctx 1 = genTmVars TyBool ctx
genETerms (TyBool) ctx n = (genTmApps TyBool ctx n) ++
                           (genTmTApps TyBool ctx n)
genETerms (TyVar i) ctx 1 = genTmVars (TyVar i) ctx
genETerms (TyVar i) ctx n = (genTmApps (TyVar i) ctx n) ++
                            (genTmTApps (TyVar i) ctx n)
genETerms typ@(TyAbs _ _) ctx 1 = genTmVars typ ctx
genETerms typ@(TyAbs _ _) ctx n = (genTmApps typ ctx n) ++
                                  (genTmTApps typ ctx n)
genETerms typ@(TyTAbs _ _) ctx 1 = genTmVars typ ctx
genETerms typ@(TyTAbs _ _) ctx n = (genTmApps typ ctx n) ++
                                   (genTmTApps typ ctx n)

-- Generates all introduction terms at type to some AST depth n
genITerms :: Type -> Context -> Int -> [Term]
genITerms _ _ 0 = []
genITerms (TyUnit) ctx 1 = [TmUnit] ++ (genETerms TyUnit ctx 1)
genITerms (TyUnit) ctx n = genETerms TyUnit ctx n
genITerms (TyBool) ctx 1 = [TmTrue, TmFalse] ++ (genETerms TyBool ctx 1)
genITerms (TyBool) ctx n = genETerms TyBool ctx n
genITerms (TyVar i) ctx n = genETerms (TyVar i) ctx n
genITerms typ@(TyAbs typ11 typ12) ctx 1 = genETerms typ ctx 1
genITerms typ@(TyAbs typ11 typ12) ctx n =
  let i = "x" ++ (show n)
      sz = sizeType typ11
      tms = genITerms typ12 ((TmBind i typ11):ctx) (n-sz-1)
      in [TmAbs i typ11 tm | tm <- tms] ++ (genETerms typ ctx n)
genITerms typ@(TyTAbs _ _) ctx 1 = genETerms typ ctx 1
genITerms typ@(TyTAbs i typ') ctx n =
  let tms = genITerms typ' ((TyBind i):ctx) (n-1)
      in [TmTAbs i tm | tm <- tms] ++ (genETerms typ ctx n)

-- Generates all elimination types to some AST depth n
genETypes :: Context -> Int -> [Type]
genETypes _ 0 = []
genETypes ctx 1 = (genTyVars ctx)
genETypes ctx n = []

-- Generates all introduction types to some AST depth n
genITypes :: Context -> Int -> [Type]
genITypes _ 0 = []
genITypes ctx 1 = [TyUnit, TyBool] ++ genETypes ctx 1
genITypes ctx n = (genTyAbs ctx n) ++ (genTyTAbs ctx n) ++ (genETypes ctx n)

-- Generates all types to some AST depth n
genTypes :: Context -> Int -> [Type]
genTypes ctx n = foldl (++) [] [genITypes ctx n' | n' <- [0..n]]

-- Generates all terms to some AST depth n
genTerms :: Type -> Context -> Int -> [Term]
genTerms typ ctx n = foldl (++) [] [genITerms typ ctx n' | n' <- [0..n]]


{-=============================== Examples ===================================-}

-- Examples are lists of tuples
data Example = Out Term
             | In Term Example
             deriving (Eq)

-- Pretty printing examples as tuples
instance Show Example where
  show e =
    let show' (Out t) = show t
        show' (In t e) = show t ++ "," ++ show' e
        in "<" ++ show' e ++ ">"

-- Projections for examples
projL :: Example -> Term
projL (Out t) = t
projL (In t _) = t

projR :: Example -> Maybe Example
projR (Out _) = Nothing
projR (In _ e) = Just e

-- Example length
lenExample :: Example -> Int
lenExample (Out trm) = 1
lenExample (In trm ex) = 1 + lenExample ex

-- Beta equality of terms
betaEqualTm :: Term -> Term -> [Id] -> Bool
betaEqualTm trm1@(TmAbs x1 typ1 _) trm2@(TmAbs x2 typ2 _) (i:is)
  | typ1 /= typ2 = False
  | otherwise = let (TmAbs _ _ trm1') = replaceTmVar x1 i trm1
                    (TmAbs _ _ trm2') = replaceTmVar x2 i trm2
                    in betaEqualTm trm1' trm2' is
betaEqualTm (TmTAbs x1 trm1) (TmTAbs x2 trm2) fvs@(i:is) =
  let trm1' = subTypeTerm x1 (TyVar i) trm1 fvs
      trm2' = subTypeTerm x2 (TyVar i) trm2 fvs
      in betaEqualTm trm1' trm2' is
betaEqualTm trm1 trm2 _ = trm1 == trm2


{-================== Generators from Type & Examples =========================-}

-- "Bad" substitution, i.e. not capture-avoiding. Necessary to fill holes. 
badSubTm :: Id -> Term -> Term -> Term
badSubTm x trm (TmUnit) = TmUnit
badSubTm x trm (TmTrue) = TmTrue
badSubTm x trm (TmFalse) = TmFalse
badSubTm x trm (TmVar i)
  | x == i    = trm
  | otherwise = TmVar i
badSubTm x trm (TmAbs i typ trm') = (TmAbs i typ rtrm)
  where rtrm = badSubTm x trm trm'
badSubTm x trm (TmApp trm1 trm2) = (TmApp trm1' trm2')
  where trm1' = badSubTm x trm trm1
        trm2' = badSubTm x trm trm2
badSubTm x trm (TmTAbs i trm') = (TmTAbs i rtrm)
  where rtrm = badSubTm x trm trm'
badSubTm x trm (TmTApp trm' typ) = (TmTApp rtrm typ)
  where rtrm = badSubTm x trm trm'

extractAbs :: Term -> Term
extractAbs (TmApp trm1@(TmAbs _ _ _) trm2) = trm1
extractAbs (TmApp trm1 trm2) = extractAbs trm1
extractAbs trm = trm

extractCtx :: Term -> Context
extractCtx (TmAbs i typ trm) = [TmBind i typ] ++ (extractCtx trm)
extractCtx (TmApp trm1 trm2) = (extractCtx trm1) ++ (extractCtx trm2)
extractCtx trm = []

checkEx :: [Term] -> [Term] -> Bool
checkEx trms outs =
  let trmouts = zip trms outs
      fvs = freshTmVars
      env = (Map.empty, fvs)
      in all (\(trm,out) -> betaEqualTm (eval trm env) out fvs) trmouts

lrnTerms :: Type -> [Example] -> Context  -> [Term] -> Int -> [Term]
lrnTerms typ exs ctx ltrms 0 = []
lrnTerms typ exs ctx [] n =
  let holes = replicate (length exs) (TmVar "$HOLE")
      in lrnTerms typ exs ctx holes n
lrnTerms typ exs@((Out _):_) ctx ltrms n =
  let ctx' = (extractCtx (extractAbs (ltrms !! 0))) ++ ctx
      htrms = genTerms typ ctx' n
      ltrms' = [[badSubTm "$HOLE" htrm ltrm | ltrm <- ltrms] |
                                              htrm <- htrms]
      otrms = [trm | (Out trm) <- exs]
      in [extractAbs trm | t@(trm:trms) <- ltrms', checkEx t otrms]
lrnTerms (TyAbs typ1 typ2) exs@((In _ _):_) ctx ltrms n =
  let i = "x" ++ show n
      strm = TmAbs i typ1 (TmVar "$HOLE")
      ftrms = [subTerm "$HOLE" strm ltrm freshTmVars | ltrm <- ltrms]
      itrms = [trm | (In trm _) <- exs]
      ltrms' = zipWith TmApp ftrms itrms
      exs' = [ex | (In _ ex) <- exs]
      in lrnTerms typ2 exs' ctx ltrms' (n-1)

