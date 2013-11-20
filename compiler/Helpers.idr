module Helpers

intersection : (Eq a) => List a -> List a -> List a
intersection a Nil = a
intersection Nil b = b
intersection a b = filter (\x => elem x b) a

difference : (Eq a) => List a -> List a -> List a
difference a Nil = a
difference Nil b = Nil
difference a b = filter (\x => not (elem x b)) a


