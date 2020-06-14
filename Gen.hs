{-|
Gen.hs
=========
Defines synthesis rules from types and examples. Guided in part by
Chapter 9 of Peter-Michael Osera's thesis, "Program Synthesis with Types".
-}

module Gen where

import SysF

{-============================= Helper Functions =============================-}
sizeType :: Type -> Int
sizeType (TyUnit) = 1
sizeType (TyBool) = 1
sizeType (TyVar _) = 1
sizeType (TyAbs typ1 typ2) = 1 + (sizeType typ1) + (sizeType typ2)
sizeType (TyTAbs _ typ) = 1 + (sizeType typ)

genTyVars :: Context -> [Type]
genTyVars ctx = [TyVar i | (TyBind i) <- ctx]

genTyAbs :: Context -> Int -> [Type]
genTyAbs ctx n =
  let cartProd xs ys = [(x,y) | x <- xs, y <- ys]
      szs = [(n1, n - 1 - n1) | n1 <- [1..(n-1)]]
      typs = [(genTypes ctx (fst sz), genTypes ctx (snd sz)) | sz <- szs]
      abss = foldl (++) [] [cartProd ty1s ty2s | (ty1s, ty2s) <- typs]
      in [TyAbs typ1 typ2 | (typ1, typ2) <- abss]

genTyTAbs :: Context -> Int -> [Type]
genTyTAbs _ 0 = []
genTyTAbs ctx n =
  let typs = genTypes ((TyBind "X"):ctx) (n-1)
      in [TyTAbs "X" typ | typ <- typs]

genTmVars :: Type -> Context -> [Term]
genTmVars typ ctx = [TmVar i | (TmBind i typ') <- ctx, typ' == typ]

genTmApps :: Type -> Context -> Int -> [Term]
genTmApps typ12 ctx n =
  let cartProd xs ys = [(x,y) | x <- xs, y <- ys]
      szs = [(n1, n - 1 - n1) | n1 <- [1..(n-1)]]
      fTyps = [t | TmBind _ t@(TyAbs _ typ12') <- ctx, typ12' == typ12]
      fxs = [(genETerms typ ctx (fst sz), genITerms typ11' ctx (snd sz)) |
             typ@(TyAbs typ11' _) <- fTyps, sz <- szs]
      apps = foldl (++) [] [cartProd fs xs | (fs, xs) <- fxs]
      in [TmApp f x | (f,x) <- apps]


{-========================== Generator Functions =============================-}
genETerms :: Type -> Context -> Int -> [Term]
genETerms _ _ 0 = []
genETerms (TyUnit) ctx 1 = genTmVars TyUnit ctx
genETerms (TyUnit) ctx n = genTmApps TyUnit ctx n
genETerms (TyBool) ctx 1 = genTmVars TyBool ctx
genETerms (TyBool) ctx n = genTmApps TyBool ctx n
genETerms typ@(TyAbs _ _) ctx 1 = genTmVars typ ctx
genETerms typ@(TyAbs _ _) ctx n = genTmApps typ ctx n

genITerms :: Type -> Context -> Int -> [Term]
genITerms _ _ 0 = []
genITerms (TyUnit) ctx 1 = [TmUnit] ++ (genETerms TyUnit ctx 1)
genITerms (TyUnit) ctx n = genETerms TyUnit ctx n
genITerms (TyBool) ctx 1 = [TmTrue, TmFalse] ++ (genETerms TyBool ctx 1)
genITerms (TyBool) ctx n = genETerms TyBool ctx n
genITerms typ@(TyAbs typ11 typ12) ctx 1 = genETerms typ ctx 1
genITerms typ@(TyAbs typ11 typ12) ctx n =
  let sz = sizeType typ11
      tms = genITerms typ12 ((TmBind "id" typ11):ctx) (n-sz-1)
      in [TmAbs "id" typ11 tm | tm <- tms] ++ (genETerms typ ctx n)

genTypes :: Context -> Int -> [Type]
genTypes _ 0 = []
genTypes ctx 1 = [TyUnit, TyBool] ++ (genTyVars ctx)
genTypes ctx n = (genTyAbs ctx n) ++ (genTyTAbs ctx n)

genTerms :: Type -> Context -> Int -> [Term]
genTerms typ ctx n = foldl (++) [] [genITerms typ ctx n' | n' <- [0..n]]
