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
  , ("match n with | 0 => True | S _ => False end",
     Match
     [(Var "n",Nothing,Nothing)]
     Nothing
     [ ([[Pattern "0" []]],Var "True")
     , ([[Pattern "S" [Wildcard]]],Var "False")
     ]
    )
  , ("let (a, b) := c in d",
     LetParen ["a","b"] Nothing (Var "c") (Var "d")
    )
  ]

shouldParseTheSame :: [(String, String)]
shouldParseTheSame =
  [ ("a → b <-> c → d", "(a → b) <-> (c → d)")
  , ("∀ x, P x → ∀ y, Q y", "∀ x, (P x → (∀ y, Q y))")
  , ("∀ P : Prop, P /\\ P \\/ P", "∀ P : Prop, (P /\\ P) \\/ P")
  , ("∀ P : Prop, P \\/ P /\\ P", "∀ P : Prop, P \\/ (P /\\ P)")
  , ("match n with | 0 => True end", "match n with 0 => True end")
  ]

main = do
  forM_ testVector $ \ (string, expected) ->
    case parseTerm string of
      Left err -> putStrLn $ "Failed to parse: " ++ string ++ "\nError: " ++ err
      Right computed ->
        case expected == computed of
          True ->
            putStrLn "✓"
          False ->
            do
              putStrLn $ "Failed on input: " ++ string
              putStrLn $ "Expected: " ++ show expected
              putStrLn $ "Computed: " ++ show computed
  forM_ shouldParseTheSame $ \ (s1, s2) ->
    case parseTerm s1 of
      Left err -> putStrLn $ "Failed to parse: " ++ s1 ++ "\nError: " ++ err
      Right c1 ->
        case parseTerm s2 of
          Left err -> putStrLn $ "Failed to parse: " ++ s2 ++ "\nError: " ++ err
          Right c2 ->
            case c1 == c2 of
              True ->
                putStrLn "✓"
              False ->
                do
                  putStrLn $ "Failed on input: " ++ show (s1, s2)
                  putStrLn $ "Left parse: " ++ show c1
                  putStrLn $ "Right parse: " ++ show c2
