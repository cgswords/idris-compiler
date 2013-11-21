module Compiler

import Helpers
import Lang 

import Effects
import Effect.State

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
-- removeAndOrNot (Fun t (pats, es)) = Fun t (pats, map removeAndOrNot es)
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

---------------------------------------------------------------------------
---------------------------------------------------------------------------
makeBeginExplicit : Expr1 -> Expr2
---------------------------------------------------------------------------

makeBeginExplicit (Lambda args e) = 
  Lambda args (Begin (map makeBeginExplicit e))
-- makeBeginExplicit (Fun t (pats, es)) = Fun t (pats, map makeBeginExplicit es)
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


---------------------------------------------------------------------------
---------------------------------------------------------------------------
uncoverAssignments : Expr2 -> Expr3
---------------------------------------------------------------------------

uncoverAssnSt : (Applicative m) => Expr2 -> Eff m [STATE (List Var)] Expr3
uncoverAssnSt (Set v e) = do xs <- get
                             newE <- uncoverAssnSt e
                             put $ union [v] xs
                             return (e3.Set v newE)
uncoverAssnSt (Lambda args e) = 
  do newE <- uncoverAssnSt e
     uncovered <- get
     ss <- return $ intersection args uncovered
     res <- return $ e3.Lambda args $ Settable ss newE
     put $ difference uncovered ss
     return res
uncoverAssnSt (Let v rhs e) =
  do origS <- get
     newRHS <- uncoverAssnSt rhs
     rhsVars <- get
     put origS
     newE <-uncoverAssnSt e
     eS <- get
     ss <- return $ intersection [v] eS
     res <- return $ e3.Let v newRHS $ Settable ss newE
     put $ union (difference eS [v]) rhsVars 
     return res
uncoverAssnSt (Letrec v rhs e) =
  do origS <- get
     newRHS <- uncoverAssnSt rhs
     newE <- uncoverAssnSt e
     ss <- get
     res <- return $ e3.Letrec v newRHS $ Settable (intersection [v] ss) newE
     put $ difference ss [v]
     return res
uncoverAssnSt (P p) = Effects.return $ P p
uncoverAssnSt (C c) = Effects.return $ C c
uncoverAssnSt (V v) = Effects.return $ V v
uncoverAssnSt (IfE e1 e2 e3) = do newe1 <- uncoverAssnSt e1
                                  newe2 <- uncoverAssnSt e2
                                  newe3 <- uncoverAssnSt e3
                                  Effects.return $ IfE newe1 newe2 newe3
uncoverAssnSt (Begin es) = do newEs <- (mapE uncoverAssnSt es)
                              Effects.return $ e3.Begin newEs
uncoverAssnSt (App es) = do newEs <- (mapE uncoverAssnSt es)
                            Effects.return $ e3.App newEs

uncoverAssignments e = runPure [List.Nil] (uncoverAssnSt e)

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


-------------------------------------------------------------------------
compiler : Esrc -> IO ()
compiler e = do let o = makeBeginExplicit $ removeAndOrNot e
                print (show o)
