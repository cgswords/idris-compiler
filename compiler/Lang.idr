module Lang 

import Helpers

%access public

public data CompPrim = Plus | Minus | Times 
                     | Car | Cdr | Cons | MTList
                     | SetCar | SetCdr
                     | PairHuh | NullHuh | BoolHuh 
                     | Box | Unbox | BoxSet | BoxHuh 
                     | EqualHuh | LT | LEQ | GT | GEQ 

instance Show CompPrim where
  show Plus = "+"
  show Minus = "-"
  show Times = "*"
  show Car = "car"
  show SetCar = "set-car!"
  show Cdr = "cdr"
  show SetCdr = "set-cdr!"
  show Cons = "cons"
  show MTList = "'()"
  show PairHuh = "pair?"
  show NullHuh = "null?"
  show BoolHuh = "bool?"
  show Box = "box"
  show Unbox = "unbox"
  show BoxSet = "box-set!"
  show BoxHuh = "box?"
  show EqualHuh = "eq?"
  show LT = "<"
  show LEQ = "<="
  show GT = ">"
  show GEQ = ">="

public data CompConst = True | False | EmptyList | Num Nat

instance Show CompConst where
  show True = "#t"
  show False = "#f"
  show EmptyList = "\'()"
  show (Num n) = show n

public data CompVar = CompVariable String

instance Show CompVar where
  show (CompVariable x) = "var_" ++ x

instance Eq CompVar where
  (CompVariable x) == (CompVariable y) = x == y

public data CompLbl = CompLabel String

instance Show CompLbl where
  show (CompLabel x) = "lbl_" ++ x

instance Eq CompLbl where
  (CompLabel x) == (CompLabel y) = x == y

----------------------------------------------------------------------------
namespace esrc
  public data Esrc = Lambda (List CompVar) (List Esrc) 
                   | App (List Esrc)
                   | P CompPrim
                   | C CompConst
                   | V CompVar
                   | Let CompVar Esrc (List Esrc)
                   | Letrec CompVar Esrc (List Esrc)
                   | IfE Esrc Esrc Esrc
                   | OrE (List Esrc)
                   | AndE (List Esrc)
                   | Not Esrc
                   | Begin (List Esrc)
                   | Set CompVar Esrc
--          | Fun Type ((List String), (List Esrc))
 
instance Show Esrc where
  show (Lambda vs e) = 
    let vars = flattenShow vs
    in "lambda (" ++ vars ++ ")." ++ (flattenShow e)
--show (Fun t (d, e)) = "Fun " ++ (flattenShow e)
  show (App es) = "(" ++ (flattenShow es) ++ ")"
  show (P p) = (show p)
  show (C c) = (show c)
  show (V v) = show v
  show (Let v rhs e) = "let " ++ (show v) ++ " = " ++ (show rhs) ++ 
                       " in " ++ (flattenShow e)
  show (Letrec v rhs e) = "letrec " ++ (show v) ++ " = " ++ (show rhs) ++ 
                          " in " ++ (flattenShow e)
  show (IfE e1 e2 e3) = "(if " ++ show e1 ++ " " ++ show e2 ++ 
                           " " ++ show e3 ++ ")"
  show (OrE es) = "(or " ++ flattenShow es ++ ")"
  show (AndE es) = "(and " ++ flattenShow es ++ ")"
  show (Not e) = "(not " ++ show e ++ ")"
  show (Begin es) = "(begin " ++ flattenShow es ++ ")"
  show (Set v e) = "(set! " ++ show v ++ " " ++ show e ++ ")"

----------------------------------------------------------------------------
namespace e1
  public data Expr1 = Lambda (List CompVar) (List Expr1) 
                    | App (List Expr1)
                    | P CompPrim
                    | C CompConst
                    | V CompVar
                    | Let CompVar Expr1 (List Expr1)
                    | Letrec CompVar Expr1 (List Expr1)
                    | IfE Expr1 Expr1 Expr1
                    | Begin (List Expr1)
                    | Set CompVar Expr1
--          | Fun Type ((List String), (List Expr1))

instance Show Expr1 where
  show (Lambda vs e) = 
    let vars = flattenShow vs
    in "lambda " ++ vars ++ "." ++ (flattenShow e)
--show (Fun t (d, e)) = "Fun " ++ (flattenShow e)
  show (App es) = "(" ++ (flattenShow es) ++ ")"
  show (P p) = (show p)
  show (C c) = (show c)
  show (V v) = show v
  show (Let v rhs e) = "let " ++ (show v) ++ " = " ++ (show rhs) ++ 
                       " in " ++ (flattenShow e)
  show (Letrec v rhs e) = "letrec " ++ (show v) ++ " = " ++ (show rhs) ++ 
                          " in " ++ (flattenShow e)
  show (IfE e1 e2 e3) = "(if " ++ show e1 ++ " " ++ show e2 ++ 
                           " " ++ show e3 ++ ")"
  show (Begin es) = "(begin " ++ flattenShow es ++ ")"
  show (Set v e) = "(set! " ++ show v ++ " " ++ show e ++ ")"
    
----------------------------------------------------------------------------
namespace e2
  public data Expr2 = Lambda (List CompVar) Expr2 
                    | App (List Expr2)
                    | P CompPrim
                    | C CompConst
                    | V CompVar
                    | Let CompVar Expr2 Expr2
                    | Letrec CompVar Expr2 Expr2
                    | IfE Expr2 Expr2 Expr2
                    | Begin (List Expr2)
                    | Set CompVar Expr2
--          | Fun Type ((List String), (List Expr2))


instance Show Expr2 where
  show (Lambda vs e) = 
    let vars = flattenShow vs
    in "lambda " ++ vars ++ "." ++ (show e)
--show (Fun t (d, e)) = "Fun " ++ (flattenShow e)
  show (App es) = "(" ++ (flattenShow es) ++ ")"
  show (P p) = (show p)
  show (C c) = (show c)
  show (V v) = show v
  show (Let v rhs e) = "let " ++ (show v) ++ " = " ++ (show rhs) ++ 
                       " in " ++ (show e)
  show (Letrec v rhs e) = "letrec " ++ (show v) ++ " = " ++ (show rhs) ++ 
                          " in " ++ (show e)
  show (IfE e1 e2 e3) = "(if " ++ show e1 ++ " " ++ show e2 ++ 
                           " " ++ show e3 ++ ")"
  show (Begin es) = "(begin " ++ flattenShow es ++ ")"
  show (Set v e) = "(set! " ++ show v ++ " " ++ show e ++ ")"

----------------------------------------------------------------------------
namespace e3
  mutual 
    public data Expr3 = Lambda (List CompVar) SBody 
                      | App (List Expr3)
                      | P CompPrim
                      | C CompConst
                      | V CompVar
                      | Let CompVar Expr3 SBody
                      | Letrec CompVar Expr3 SBody
                      | IfE Expr3 Expr3 Expr3
                      | Begin (List Expr3)
                      | Set CompVar Expr3
--            | Fun Type ((List String), (List Expr3))
    
    public data SBody = Settable (List CompVar) Expr3


---- This is the dirtiest hack; it seems that you can't define mutually-recursive Show instances (?)
------ Maybe file a bug report about that later.
showSet : SBody -> String

instance Show Expr3 where
  show (Lambda vs ss) = 
    let vars = flattenShow vs
    in "lambda " ++ vars ++ ". " ++ showSet ss
  show (App es) = "(" ++ (flattenShow es) ++ ")"
  show (P p) = (show p)
  show (C c) = (show c)
  show (V v) = show v
  show (Let v rhs ss) = 
    "let " ++ (show v) ++ " = " ++ (show rhs) ++ " in " ++ showSet ss
  show (Letrec v rhs ss) = "letrec " ++ (show v) ++ " = " ++ (show rhs) ++ 
                          " in " ++ showSet ss
  show (IfE e1 e2 e3) = "(if " ++ show e1 ++ " " ++ show e2 ++ 
                           " " ++ show e3 ++ ")"
  show (Begin es) = "(begin " ++ flattenShow es ++ ")"
  show (Set v e) = "(set! " ++ show v ++ " " ++ show e ++ ")"

showSet (Settable vs e) =  "[set " ++ (flattenShow vs) ++ "] " ++ (show e)

instance Show SBody where
  show (Settable vs e) = "[settables: " ++ (flattenShow vs) ++ "] " ++ (show e)

----------------------------------------------------------------------------
namespace e4
  public data Expr4 = Lambda (List CompVar) Expr4 
                    | App (List Expr4)
                    | P CompPrim
                    | C CompConst
                    | V CompVar
                    | Let CompVar Expr4 Expr4
                    | Letrec CompVar Expr4 Expr4
                    | IfE Expr4 Expr4 Expr4
                    | Begin (List Expr4)
--          | Fun Type ((List String), (List Expr2))


instance Show Expr4 where
  show (Lambda vs e) = 
    let vars = flattenShow vs
    in "lambda " ++ vars ++ "." ++ (show e)
  show (App es) = "(" ++ (flattenShow es) ++ ")"
  show (P p) = (show p)
  show (C c) = (show c)
  show (V v) = show v
  show (Let v rhs e) = "let " ++ (show v) ++ " = " ++ (show rhs) ++ 
                       " in " ++ (show e)
  show (Letrec v rhs e) = "letrec " ++ (show v) ++ " = " ++ (show rhs) ++ 
                          " in " ++ (show e)
  show (IfE e1 e2 e3) = "(if " ++ show e1 ++ " " ++ show e2 ++ 
                           " " ++ show e3 ++ ")"
  show (Begin es) = "(begin " ++ flattenShow es ++ ")"

----------------------------------------------------------------------------
namespace e5
  mutual
    public data Expr5 = App (List Expr5)
                      | P CompPrim
                      | C CompConst
                      | V CompVar
                      | Let CompVar Expr5 Expr5
                      | Letrec CompVar e5.LForm Expr5
                      | IfE Expr5 Expr5 Expr5
                      | Begin (List Expr5)
    public data LForm = Lambda (List CompVar) e5.FVars Expr5
    public data FVars = Frees (List CompVar)

showE5LForm : e5.LForm -> String
showE5FVars : e5.FVars -> String

instance Show Expr5 where
  show (App es) = "(" ++ (flattenShow es) ++ ")"
  show (P p) = (show p)
  show (C c) = (show c)
  show (V v) = show v
  show (Let v rhs e) = 
    "let " ++ (show v) ++ " = " ++ (show rhs) ++ " in " ++ (show e)
  show (Letrec v rhs e) = "letrec " ++ (show v) ++ " = " ++ (showE5LForm rhs) ++ 
                          " in " ++ show e
  show (IfE e1 e2 e3) = "(if " ++ show e1 ++ " " ++ show e2 ++ 
                           " " ++ show e3 ++ ")"
  show (Begin es) = "(begin " ++ flattenShow es ++ ")"

showE5LForm (Lambda vs f e) =
    let vars = flattenShow vs in
    let fs = showE5FVars f  
    in "lambda " ++ vars ++ ". " ++ fs ++ show e

showE5FVars (Frees vs) =  "[free " ++ (flattenShow vs) ++ "] "

----------------------------------------------------------------------------
namespace e6
  mutual
    public data Expr6 = App (List Expr6)
                      | P CompPrim
                      | C CompConst
                      | V CompVar
                      | Let CompVar Expr6 Expr6
                      | Letrec CompLbl e6.LForm CForm Expr6
                      | IfE Expr6 Expr6 Expr6
                      | Begin (List Expr6)
    public data LForm = Lambda (List CompVar) e6.FVars Expr6
    public data CForm = Closure (CompVar, CompLbl, (List CompVar)) Expr6
    public data FVars = Frees (List CompVar)

