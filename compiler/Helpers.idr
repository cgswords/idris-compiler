module Helpers

%access public

flattenShow : (Show a) => (List a) -> String
flattenShow Nil = ""
flattenShow (x::ls) = show x ++ " " ++ flattenShow ls

unique : (Eq a) => List a -> List a
unique [] = []
unique (x::ls) = if elem x ls then unique ls else x::(unique ls)

union : (Eq a) => List a -> List a -> List a
union a Nil = a
union Nil b = b 
union a b = let mapper = (\ x => \ ls => if elem x b then ls else (List.(::) x ls))
            in foldr mapper b a

intersection : (Eq a) => List a -> List a -> List a
intersection a Nil = a
intersection Nil b = b
intersection a b = filter (\x => elem x b) a

difference : (Eq a) => List a -> List a -> List a
difference a Nil = a
difference Nil b = Nil
difference a b = filter (\x => not (elem x b)) a


