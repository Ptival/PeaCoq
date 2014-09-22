import Control.Monad (forM_)
import Parser

op :: String -> Term -> Term -> Term
op operator a b = App (App (Var operator) a) b

infixr 0 →

(→) :: Term -> Term -> Term
a → b = Arrow a b

infix 1 ^=, ^^=

(^=) :: Term -> Term -> Term
(^=) = op "eq"

(^^=) :: String -> String -> Term
a ^^= b = Var a ^= Var b

infixl 2 ^+, ^^+

(^+) :: Term -> Term -> Term
(^+) = op "plus"

(^^+) :: String -> String -> Term
a ^^+ b = Var a ^+ Var b

testVector :: [(String, Term)]
testVector =
  -- simple variable
  [ ("a", Var "a")
  -- equality
  , ("a = 42", "a" ^^= "42")
  -- arrow/equal precedence
  , ("∀ a b : comparison, a = Eq → b = Eq → a = b",
     Forall
     [MkBinder [Just "a", Just "b"] (Just (Var "comparison"))]
     ("a" ^^= "Eq" → "b" ^^= "Eq" → "a" ^^= "b")
    )
  -- equal/plus precedence
  , ("∀ n : nat, 0 + n = n",
     Forall
     [MkBinder [Just "n"] (Just (Var "nat"))]
     (("0" ^^+ "n") ^= (Var "n")))
  -- plus associativity, application/plus precedence
  , ("∀ p : nat, S n + (m + p) = S n + m + p",
     Forall
     [MkBinder [Just "p"] (Just (Var "nat"))]
     (
       ((App (Var "S") (Var "n")) ^+ ("m" ^^+ "p"))
       ^= ((App (Var "S") (Var "n")) ^+ Var "m") ^+ Var "p")
    )
  -- quantifiers
  , ("∀ a b (c d : a) e, False",
     Forall
     [ MkBinder [Just "a", Just "b"] Nothing
     , MkBinder [Just "c", Just "d"] (Just (Var "a"))
     , MkBinder [Just "e"] Nothing
     ]
     (Var "False")
    )
  ]

main = do
  forM_ testVector $ \ (string, expected) ->
    let computed = parseTerm string in
    case expected == computed of
      True ->
        putStrLn "✓"
      False ->
        do
          putStrLn $ "Failed on input: " ++ string
          putStrLn $ "Expected: " ++ show expected
          putStrLn $ "Computed: " ++ show computed
