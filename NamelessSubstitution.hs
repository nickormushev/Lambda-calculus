data Term = Lambda Term | Var Int | App Term Term --deriving(Show)
data Substitution = Pair Int Term

instance Show Term where                     
    show (Lambda t) = "(\\" ++ show(t) ++ ")"
    show (App m n) = "(" ++ show m ++ show n ++ ")"
    show (Var x) = show x

--addOne Test
--addOne (App (Var 1) (Lambda (App (Var 0) (Lambda (App (Var 0) (Var 3)))))) 1 (the second argument means we are inside one lambda)
-- 1(\0(\03)) -> 2(\0(\04)) 1 and 3 need to be incresed to 2 and 4 because we entered a lambda. Meaning their index increases by one
--addOne adds one to all free variables. Used when entering a lambda term 
addOne :: Term -> Int -> Term
addOne (Var x) lambdaCount
    | isFree    = Var (x + 1)
    | otherwise = Var x
  where isFree  = x - lambdaCount >= 0 --Using that the De bruij index of bounded variables is negative

addOne (App t1 t2) lambdaCount = App (addOne t1 lambdaCount)  (addOne t2 lambdaCount)
addOne (Lambda t) lambdaCount = Lambda $ addOne t $ lambdaCount + 1


--substitution (App (Var 0) (Lambda (App (Var 0) (Lambda (App (Var 1) (App (Var 0) (Var 2))))))) (Pair 0 (App (Var 1) (Lambda (Var 0)))) 0
--0(\0(\1(02)))[0 -> 1\0] -> (1\0)(\0(\1(0(3\0)))) 
--substitution (App (Lambda (Lambda (Var 2))) (Lambda (App (Var 0) (Lambda (App (Var 1) (App (Var 0) (Var 2))))))) 
--             (Pair 0 (App (Var 1) (Lambda (Var 0)))) 0 (Almost the same example more lambdas (\(\2))(\0(\1(02)))[0 -> 1\0]
substitution :: Term -> Substitution -> Int -> Term
substitution z@(Var x) (Pair y t) _ 
    | x == y    = t
    | otherwise = z
substitution (App x y) s lambdaCount = App (substitution x s lambdaCount) (substitution y s lambdaCount)
--When entering a lambda term the values of all free variables in the substitution must be increased by one
substitution (Lambda t) (Pair y oldTerm) lambdaCount = Lambda $ substitution t (Pair (y + 1) $ (addOne oldTerm lambdaCount)) (lambdaCount + 1)

main :: IO () 
main = do
    term <- getLine
    return()
