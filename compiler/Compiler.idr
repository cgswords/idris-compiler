module Compiler

import Effects
import Effect.State
import Control.Monad.Identity

import Lang 
import Helpers
import Tests

%access public

---------------------------------------------------------------------------
---------------------------------------------------------------------------
removeAnd : (List Esrc) -> Expr1
removeOr : (List Esrc) -> Expr1
removeNot : Esrc -> Expr1
removeAndOrNot : Esrc -> Expr1
---------------------------------------------------------------------------

removeAnd Nil = (e1.C True)
removeAnd ((esrc.C True)::ls) = removeAnd ls
removeAnd ((esrc.C False)::ls) = e1.C False
removeAnd (x::Nil) = removeAndOrNot x
removeAnd (x::ls) = e1.IfE (removeAndOrNot x) (removeAnd ls) (e1.C False)

removeOr Nil = (e1.C False)
removeOr ((esrc.C True)::ls) = e1.C True
removeOr ((esrc.C False)::ls) = removeOr ls
removeOr (x::Nil) = removeAndOrNot x
removeOr (x::ls) = e1.IfE (removeAndOrNot x) (e1.C True) (removeOr ls)

removeNot e = IfE (removeAndOrNot e) (C False) (C True)

removeAndOrNot (AndE ls) = removeAnd ls
removeAndOrNot (OrE ls) = removeOr ls
removeAndOrNot (Not e) = removeNot e
removeAndOrNot (Lambda args es) = Lambda args $ map removeAndOrNot es
removeAndOrNot (App es) = App (map removeAndOrNot es)
removeAndOrNot (P p) = P p
removeAndOrNot (C c) = C c
removeAndOrNot (V v) = V v
removeAndOrNot (Let v rhs e) = 
  Let v (removeAndOrNot rhs) (map removeAndOrNot e)
removeAndOrNot (Letrec v rhs e) = 
  Letrec v (removeAndOrNot rhs) (map removeAndOrNot e)
removeAndOrNot (IfE e1 e2 e3) = 
  IfE (removeAndOrNot e1) (removeAndOrNot e2) (removeAndOrNot e3)
removeAndOrNot (Begin es) = Begin (map removeAndOrNot es)
removeAndOrNot (Set v e) = Set v (removeAndOrNot e)
-- removeAndOrNot (Fun t (pats, es)) = Fun t (pats, map removeAndOrNot es)

---------------------------------------------------------------------------
---------------------------------------------------------------------------
makeBeginExplicit : Expr1 -> Expr2
---------------------------------------------------------------------------

makeBeginExplicit (Lambda args e) = 
  Lambda args (Begin (map makeBeginExplicit e))
makeBeginExplicit (App es) = App (map makeBeginExplicit es)
makeBeginExplicit (P p) = P p
makeBeginExplicit (C c) = C c
makeBeginExplicit (V v) = V v
makeBeginExplicit (Let v rhs e) = 
  Let v (makeBeginExplicit rhs) (Begin (map makeBeginExplicit e))
makeBeginExplicit (Letrec v rhs e) = 
  Letrec v (makeBeginExplicit rhs) (Begin (map makeBeginExplicit e))
makeBeginExplicit (IfE e1 e2 e3) = 
  IfE (makeBeginExplicit e1) (makeBeginExplicit e2) (makeBeginExplicit e3)
makeBeginExplicit (Begin es) = Begin (map makeBeginExplicit es)
makeBeginExplicit (Set v e) = Set v (makeBeginExplicit e)
-- makeBeginExplicit (Fun t (pats, es)) = Fun t (pats, map makeBeginExplicit es)

------------------------------------------------------------------------
---------------------------------------------------------------------
uncoverAssignments : Expr2 -> Expr3
---------------------------------------------------------------------------

uncoverAssnSt : Expr2 -> Eff Identity [STATE (List CompVar)] Expr3

uncoverAssnSt (Set v e) = do xs <- get
                             newE <- uncoverAssnSt e
                             put $ union [v] xs
                             return (e3.Set v newE)
uncoverAssnSt (Lambda args e) = 
  do newE <- uncoverAssnSt e
     uncovered <- get
     let ss = intersection args uncovered
     let res = e3.Lambda args $ Settable ss newE
     put $ difference uncovered args
     return res
uncoverAssnSt (Let v rhs e) =
  do origS <- get
     newRHS <- uncoverAssnSt rhs
     letSets <- get
     put origS
     newE <- uncoverAssnSt e
     sets <- get
     let letv = intersection [v] sets
     let valv = union letSets (difference sets [v]) 
     let res = e3.Let v newRHS $ Settable letv newE
     put valv
     return res
uncoverAssnSt (Letrec v rhs e) =
  do origS <- get
     newRHS <- uncoverAssnSt rhs
     letSets <- get
     put origS
     newE <- uncoverAssnSt e
     sets <- get
     let letv = intersection [v] sets
     let valv = union letSets (difference sets [v]) 
     let res = e3.Letrec v newRHS $ Settable letv newE
     put valv
     return res
uncoverAssnSt (P p) = Effects.return $ P p
uncoverAssnSt (C c) = Effects.return $ C c
uncoverAssnSt (V v) = Effects.return $ V v
uncoverAssnSt (IfE e1 e2 e3) = do newe1 <- uncoverAssnSt e1
                                  newe2 <- uncoverAssnSt e2
                                  newe3 <- uncoverAssnSt e3
                                  Effects.return $ IfE newe1 newe2 newe3
uncoverAssnSt (Begin es) = do newEs <- mapE uncoverAssnSt es
                              Effects.return $ e3.Begin newEs
uncoverAssnSt (App es) = do newEs <- mapE uncoverAssnSt es
                            Effects.return $ e3.App newEs

runId : Identity a -> a
runId (Id f) = f

uncoverAssignments e = runId $ run [List.Nil] $ uncoverAssnSt e

---------------------------------------------------------------------------
---------------------------------------------------------------------------
purifyLetrec : Expr3 -> Expr3
---------------------------------------------------------------------------

e3LamExp : Expr3 -> Bool

e3LamExp (Lambda vs s) = True
e3LamExp x = False

purifyLetrec (Lambda vs (Settable ss e)) = 
  Lambda vs (Settable ss (purifyLetrec e))
purifyLetrec (Let v rhs (Settable ss e)) = 
  Let v (purifyLetrec rhs) (Settable ss (purifyLetrec e))
purifyLetrec (Letrec v rhs (Settable ss e)) =
  if (e3LamExp rhs)
  then Letrec v rhs (Settable ss (purifyLetrec e))
  else Let v rhs (Settable ss (purifyLetrec e))
purifyLetrec (IfE e1 e2 e3) = 
  IfE (purifyLetrec e1) (purifyLetrec e2) (purifyLetrec e3)
purifyLetrec (App es) = App (map purifyLetrec es)
purifyLetrec (Begin es) = Begin (map purifyLetrec es)
purifyLetrec (Set v rhs) = Set v (purifyLetrec rhs)
purifyLetrec x = x

---------------------------------------------------------------------------
---------------------------------------------------------------------------
convertAssignments : Expr3 -> Expr4
---------------------------------------------------------------------------

uniqueVar : String -> Eff Identity [STATE Int] CompVar
uniqueVar s = do var <- get
                 put (var + 1)
                 Effects.return $ CompVariable (s ++ "." ++ (show var))

uniqueLbl : String -> Eff Identity [STATE Int] CompLbl
uniqueLbl s = do var <- get
                 put (var + 1)
                 Effects.return $ CompLabel (s ++ "$" ++ (show var))

uniqueId : CompVar -> Eff Identity [STATE Int] CompVar
uniqueId (CompVariable s) = uniqueVar s

newBindings : (List CompVar) -> Eff Identity [STATE Int] (List (CompVar, CompVar))
newBindings List.Nil = Effects.return $ List.Nil
newBindings (x::ls) = Effects.return $ the (List _) ((x,!(uniqueId x))::(!(newBindings ls)))

maybeReplace : (List (CompVar, CompVar)) -> CompVar -> CompVar
maybeReplace List.Nil v = v
maybeReplace ((x,bind)::ls) v = if x == v then bind else maybeReplace ls v

namespace convAssn
  buildInner : (List (CompVar, CompVar)) -> Expr4 -> Expr4
  buildInner List.Nil e = e
  buildInner ((v,bind)::ls) e = 
    e4.Let v (e4.App [(P Cons), (V bind), (P MTList)]) (buildInner ls e)

  replaceVars : Expr4 -> (List CompVar) -> Expr4
  replaceVars (Lambda args body) env = Lambda args (replaceVars body env)
  replaceVars (App ((P SetCar)::((V v)::rhs))) env = App (the (List Expr4) 
                                                    ((P SetCar)::
                                                      ((V v)::(map (\ e => replaceVars e env) rhs))))
  replaceVars (V v)              env = if v `elem` env 
                                       then (App (the (List Expr4) [(P Car), (V v)]))
                                       else (V v)
  replaceVars (Let v rhs e)      env = Let v (replaceVars rhs env) (replaceVars e env)
  replaceVars (Letrec v rhs e)   env = Letrec v (replaceVars rhs env) (replaceVars e env)
  replaceVars (IfE e1 e2 e3)     env = IfE (replaceVars e1 env)
                                           (replaceVars e2 env)
                                           (replaceVars e2 env)
  replaceVars (Begin es)         env = Begin (map (\ e => replaceVars e env) es)
  replaceVars (App es)           env = App (map (\ e => replaceVars e env) es)
  replaceVars (P p)              env = (P p)
  replaceVars (C c)              env = (C c)

  expr : Expr3 -> Eff Identity [STATE Int] Expr4
  expr (Set v e) = 
    Effects.return $ App (the (List _) [(e4.P SetCar), (V v), !(expr e)])
  expr (Lambda args (Settable ss e)) =
    if (ss == List.Nil)
    then Effects.return $ Lambda args !(expr e)
    else do pairing <- newBindings ss
            recE <- expr e
            let newE = replaceVars recE ss
            let inner = buildInner pairing newE
            let newArgs = map (maybeReplace pairing) args
            Effects.return $ Lambda newArgs inner
  expr (Let v rhs (Settable ss e)) = 
    if (ss == List.Nil)
    then Effects.return $ Let v !(expr rhs) !(expr e)
    else do newRHS <- expr rhs 
            pairing <- newBindings ss
            recE <- expr e
            let newE = replaceVars recE ss
            let inner = buildInner pairing newE
            Effects.return $ Let (maybeReplace pairing v) newRHS inner
  expr (Letrec v rhs (Settable ss e)) =
    Effects.return $ Letrec v !(expr rhs) !(expr e)
  expr (IfE e1 e2 e3) = 
    Effects.return $ IfE !(expr e1) !(expr e2) !(expr e3)
  expr (Begin es) = Effects.return $ Begin !(mapE expr es)
  expr (App es) = Effects.return $ App !(mapE expr es)
  expr (P p) = Effects.return $ P p
  expr (C c) = Effects.return $ C c
  expr (V v) = Effects.return $ V v

convertAssignments e = runId $ run [10000] $ convAssn.expr e

---------------------------------------------------------------------------
---------------------------------------------------------------------------
removeAnonymousLambda : Expr4 -> Expr4
---------------------------------------------------------------------------

mutual

namespace rAL
  mutual
    boundExp : Expr4 -> Eff Identity [STATE Int] Expr4
    boundExp (Lambda xs e) = Effects.return $ Lambda xs !(rAL.expr e)
    boundExp (Let v rhs e) = Effects.return $ Let v !(rAL.boundExp rhs) !(rAL.expr e)
    boundExp x = rAL.expr x

-- uniqueId : CompVar -> Eff Identity [STATE Int] CompVar
    expr : Expr4 -> Eff Identity [STATE Int] Expr4
    expr (Lambda xs e) = do anonV <- uniqueVar "anon"
                            Effects.return $ Letrec anonV (Lambda xs !(rAL.expr e)) (V anonV)
    expr (Let v rhs e) = Effects.return $ Let v !(rAL.boundExp rhs) !(rAL.expr e)
    expr (Letrec v (Lambda xs body) e) = 
      Effects.return $ Letrec v (Lambda xs !(rAL.expr body)) !(rAL.expr body)
    expr (IfE e1 e2 e3) = Effects.return $ IfE !(rAL.expr e1) !(rAL.expr e2) !(rAL.expr e3) 
    expr (App es) = Effects.return $ App !(mapE rAL.expr es)
    expr (Begin es) = Effects.return $ Begin !(mapE rAL.expr es)
    expr (C c) = Effects.return $ (C c)
    expr (P p) = Effects.return $ (P p)
    expr (V v) = Effects.return $ (V v)

removeAnonymousLambda e = runId $ run [20000] $ rAL.expr e

---------------------------------------------------------------------------
---------------------------------------------------------------------------
sanitizeBindingForms : Expr4 -> Expr4
---------------------------------------------------------------------------

namespace sBF
  expr : Expr4 -> Expr4
  expr (Let v (Lambda xs body) e) = Letrec v (Lambda xs (expr body)) (expr e)
  expr (Let v rhs e) = Let v (expr rhs) (expr e)
  expr (Letrec v (Lambda xs body) e) = Letrec v (Lambda xs (expr body)) (expr e)
  expr (IfE e1 e2 e3) = IfE (expr e1) (expr e2) (expr e3)
  expr (App es) = App (map expr es)
  expr (Begin es) = Begin (map expr es)
  expr x = x

sanitizeBindingForms = sBF.expr

---------------------------------------------------------------------------
---------------------------------------------------------------------------
uncoverFree : Expr4 -> Expr5
---------------------------------------------------------------------------

namespace uF
  expr : Expr4 -> (Expr5, (List CompVar))
  expr (Let x rhs body) = 
    let (newBody, bodyFrees) = uF.expr body in
    let (newRHS, rhsFrees) = uF.expr rhs in
    (Let x newRHS newBody, difference (union rhsFrees bodyFrees) (the (List CompVar) [x]))
  expr (Letrec x (Lambda xs rhs) body) =
    let (newRHS, rhsFrees) = uF.expr rhs in
    let (newBody, bodyFrees) = uF.expr body in
    let bindList = (the (List CompVar) [x]) in
    let freesForm = e5.Frees (difference rhsFrees (union bindList xs)) in
    let newExpr = Letrec x (Lambda xs freesForm newRHS) newBody in
    let newFrees = difference (union rhsFrees bodyFrees) bindList in
    (newExpr, newFrees)
  expr (IfE e1 e2 e3) = 
    let (ne1, nef1) = uF.expr e1 in
    let (ne2, nef2) = uF.expr e2 in
    let (ne3, nef3) = uF.expr e3 in
    (IfE ne1 ne2 ne3, (union nef1 (union nef2 nef3)))
  expr (Begin es) = 
    let recs = map uF.expr es in
    let newEs = map fst recs in
    let frees = map snd recs in
    (Begin newEs, foldr union List.Nil frees)
  expr (App es) = 
    let recs = map uF.expr es in
    let newEs = map fst recs in
    let frees = map snd recs in
    (App newEs, foldr union List.Nil frees)
  expr (C c) = ((C c), List.Nil)
  expr (P p) = ((P p), List.Nil) 
  expr (V v) = ((V v), (the (List CompVar) [v]))

uncoverFree e = let (e, f) = uF.expr e in e

---------------------------------------------------------------------------
---------------------------------------------------------------------------
convertClosures : Expr5 -> Expr6
---------------------------------------------------------------------------
--namespace e6
--public data Expr6 = App (List Expr6)
--                  | P CompPrim
--                  | C CompConst
--                  | V CompVar
--                  | Let CompVar Expr6 Expr6
--                  | Letrec CompLbl e6.LForm CForm Expr6
--                  | IfE Expr6 Expr6 Expr6
--                  | Begin (List Expr6)
--public data LForm = Lambda (List CompVar) e6.FVars Expr6
--public data CForm = Closure (CompVar, CompLbl, (List CompVar)) Expr6
--public data FVars = Frees (List CompVar)

namespace cC
  expr : Expr5 -> Eff Identity [STATE Int] Expr6
  expr (Letrec (CompVariable s) (Lambda xs (Frees fs) rhs) e) = 
    do newLbl <- uniqueLbl s
       closVar <- uniqueVar "cp"
       Effects.return $ 
        Letrec newLbl 
               (e6.Lambda (closVar::xs) (e6.Frees (closVar::fs)) !(cC.expr rhs)) 
               (e6.Closure ((CompVariable s), newLbl, fs))
               !(cC.expr e)
               -- (Lambda (closVar::xs) (e6.Frees (closVar::fs)) !(cC.expr rhs)) 
  expr (App ((V v)::es)) = Effects.return $ App ((V v)::(V v)::(!(mapE cC.expr es)))
  expr (App ((P p)::es)) = Effects.return $ App ((P p)::(!(mapE cC.expr es)))
  expr (App (x::es)) = do uid <- uniqueVar "tmp"
                          let e = e6.Let uid 
                                    !(expr x) 
                                    (App ((V uid)::(V uid)::(!(mapE cC.expr es))))
                          Effects.return e 
  expr (Let v rhs e) = Effects.return $ Let v !(expr rhs) !(cC.expr e)
  expr (IfE e1 e2 e3) = Effects.return $ IfE !(cC.expr e1) !(cC.expr e2) !(cC.expr e3)
  expr (Begin es) = Effects.return $ Begin !(mapE cC.expr es)
  expr (P p) = Effects.return $ (P p)
  expr (C c) = Effects.return $ (C c)
  expr (V v) = Effects.return $ (V v)

convertClosures e = runId $ run [30000] $ cC.expr e

---------------------------------------------------------------------------
----  (optimize-known-call)
--  (introduce-procedure-primitives)
--  (lift-letrec)
--  (normalize-context)
--  (specify-representation)
----  (fold-constants)
--  (uncover-locals)
--  (remove-let)
--  (verify-uil)
--  (remove-complex-opera*)
--  (flatten-set!)
--  (impose-calling-conventions)
--  (expose-allocation-pointer)
--  (uncover-frame-conflict)
--  (pre-assign-frame)
--  (assign-new-frame)
-- (iterate
--    (finalize-frame-locations)
--    (select-instructions)
--    (uncover-register-conflict)
--    (assign-registers)
--    (break/when everybody-home?)
--    (assign-frame))
--  (discard-call-live)
--  (finalize-locations)
--  (expose-frame-var)
--  (expose-memory-operands)
--  (expose-basic-blocks)
----  (optimize-jumps)
--  (flatten-program)
--  (generate-x86-64 assemble)

----------------------------------------------------------------------
compiler : Esrc -> String 
compiler e = do let o = uncoverFree
                        $ sanitizeBindingForms
                        $ removeAnonymousLambda
                        $ convertAssignments 
                        $ purifyLetrec 
                        $ uncoverAssignments 
                        $ makeBeginExplicit 
                        $ removeAndOrNot e
                (show o)
