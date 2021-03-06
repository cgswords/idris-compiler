module Tests

import Lang
import Helpers

%access public

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---------------------------------------------------------------------------
x : CompVar
x = CompVariable "x"
y : CompVar
y = CompVariable "y"

vT : Esrc
vT = esrc.C True

t1 : Esrc
t1 = Lambda [x] [(V x)]

t2 : Esrc
t2 = esrc.Lambda [x]
           [(AndE [vT, (OrE [vT, (esrc.V x)])])]

t3 : Esrc
t3 = esrc.App [(esrc.Lambda [x] [(esrc.App [(esrc.P Plus), (esrc.V x), (C (Num 5))])]), (C (Num 6))]

t4 : Esrc
t4 = esrc.Letrec y vT 
       [(esrc.Let x (esrc.Lambda [x] [(esrc.App [(esrc.P Plus), (esrc.V x), (C (Num 5))])])
          [(esrc.IfE vT (esrc.App [(esrc.V x), (esrc.V y)]) (esrc.V y))])]

t5 : Esrc
t5 = Lambda [x,y] [(Set x (C (Num 5))), (Set y (V x)), (esrc.App [(esrc.P Plus), (esrc.V x), (V y)])]
