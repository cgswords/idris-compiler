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
removeAndOrNot (Fun t (pats, es)) = Fun t (pats, map removeAndOrNot es)
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
makeBeginExplicit (Fun t (pats, es)) = Fun t (pats, map makeBeginExplicit es)
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

uncoverAssnSt : Expr2 -> Eff m [STATE (List Var)] Expr3
uncoverAssnSt (Set v e) = do xs <- get
                             let newls = List.(::) v xs
                             put newls
                             return (e3.Set v (uncoverAssnSt e))
uncoverAssnSt (Lambda args e) = 
  do es <- map uncoverAssnSt e
     uncovered <- get
     ss <- intersection args uncovered
     res <- Settable (intersection args uncovered) es
     put $ difference uncovered ss
     return res
uncoverAssnSt (P p) = return P p
uncoverAssnSt (C c) = return C c
uncoverAssnSt (V v) = return V v

-- I should deal with let/letrec next, but those bindings are going to be a
-- do-style mess and I'm feeling lazy tonight.

uncoverAssignments e = runPure [List.Nil] (uncoverAssnSt e)

------------------------------------------------------------------------

compiler : Esrc -> IO ()
compiler e = do let o = makeBeginExplicit $ removeAndOrNot e
                print (show o)
