data Term = Lambda String Term | Var String | App Term Term
data Substitution = Pair String Term

--Examples
--substitution (Lambda "y" (Lambda "y" (Lambda "y" (Lambda "y" (Lambda "y" (Lambda "y" (Var "t"))))))) (Pair "t" (Var "y")) 0
-- (\y(\y(\y(\y(\y(\y t))))))[t -> y] = (\a(\a(\a(\a(\a(\a y))))))
--substitution (Lambda "y" (App (App (Var "y") (Var "t")) (Lambda "l" (Var "l")))) (Pair "t" (Var "y")) 0
-- (\y (y t) (\l l)) [t -> y] = (\a (a y) (\l l))

instance Show Term where                     
    show (Lambda x t) = "(\\" ++ show(x) ++ show(t) ++ ")"
    show (App m n) = "(" ++ show m ++ show n ++ ")"
    show (Var x) = "\""++ x ++ "\"" 

findBoundedVariables :: Term -> [String]
findBoundedVariables (Lambda x t) = x : findBoundedVariables t
findBoundedVariables (App x y) =  findBoundedVariables x ++ findBoundedVariables y
findBoundedVariables (Var x) = []

findFreeVariables :: Term -> [String]
findFreeVariables (Lambda x t) = filter (\t -> t /= x) $ findFreeVariables t
findFreeVariables (App x y) = findFreeVariables x ++ findFreeVariables y
findFreeVariables (Var x) = x : []

--Tells if a character is in a string or an array of characters
contains :: String -> [String] -> Bool
contains x s = (filter (\v -> v == x) s) /= []

--This verifies that we can use the partial substitution and just continue the substitution inside a lambda
canUsePartialSubstitution :: Term -> Substitution -> Bool
canUsePartialSubstitution (Lambda x t) (Pair y s) =
    (not $ contains y $ findFreeVariables t) || (not $ contains x $ findFreeVariables s)

--generates a character that is from a..z and is not contained in the given [Char] array. 
--Used to generate new unused chars for curry substitution.
generateChar :: [String] -> Int -> String
generateChar used next   
    | xIsUsed = generateChar used $ next + 1
    | otherwise     = "x" ++ show(next)
  where xIsUsed = contains ("x" ++ show(next)) used

substitution :: Term -> Substitution -> Int -> Term
--currIndex determines which x we have reached
--substitues y with t (if x == y) and does nothing if x != y
substitution z@(Var x) (Pair y t) currIndex
    | x == y    = t
    | otherwise = z
substitution (App x y) s currIndex = App (substitution x s currIndex) (substitution y s currIndex)
--These are the cases of the curry substitution written in code
substitution z@(Lambda x t) q@(Pair y s) currIndex
    | x == y  = z
    | canUsePartialSubstitution z q = (Lambda x $ substitution t q currIndex)
    | otherwise = (Lambda newChar (substitution (substitution t (Pair x (Var newChar)) currIndex) q currIndex))
  where newChar = generateChar (findFreeVariables t ++ findFreeVariables s) currIndex

main :: IO () 
main = do
    return()
