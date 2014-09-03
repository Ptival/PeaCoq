{
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}

module Parser where

import Control.Monad
import Data.Char (isSpace, isAlpha, isDigit)
import Data.Typeable
import GHC.Generics

import Lexer
}

%name parse
%tokentype { Token }
%error { parseError }

%token

var { TokSym $$ }
'(' { TokLParen }
')' { TokRParen }
'→' { TokArrow }
'λ' { TokLambda }
':' { TokColon }
'@' { TokAnnot }
'=' { TokEq }
'_' { TokUnderscore }
'?' { TokHole }
"Type" { TokType }
"let" { TokLet }
"in" { TokIn }

-- low precedence
%right '@'
%nonassoc LAM
%right '→'
%nonassoc '(' ')'
%left var '?' "Type"
-- high precedence

%%

Term :
var                             { Var () $1 }
| "Type"                        { Type () }
| Term '@' Term                 { Annot () $1 $3 }
| '(' var ':' Term ')' '→' Term { Pi () (Just $2) $4 $7 }
| Term '→' Term                 { Pi () Nothing $1 $3 }
| 'λ' var Term %prec LAM        { Lam () (Just $2) $3 }
| 'λ' '_' Term %prec LAM        { Lam () Nothing $3 }
| '(' Term ')'                  { $2 }
| Term Term %prec var           { App () $1 $2 }
| '?'                           { Hole () }
| "let" var '=' Term "in" Term  { Let () (Just $2) $4 $6 }
| "let" '_' '=' Term "in" Term  { Let () Nothing $4 $6 }

{

parseError :: [Token] -> a
parseError l = error $ "Parse error on: " ++ show l

type Name = String

data Term a
  = Type a
  | Pi a (Maybe Name) (Type a) (Term a)
  | Var a Name
  | Lam a (Maybe Name) (Term a)
  | App a (Term a) (Term a)
  | Let a (Maybe Name) (Term a) (Term a)
  | Annot a (Term a) (Type ())
  | Hole a
  deriving (Eq, Generic, Typeable, Show)
type Type = Term

pprintPar t = "(" ++ pprint t ++ ")"

pprintParIf p t | p t = pprintPar t
pprintParIf p t | otherwise = pprint t

isApp (App _ _ _) = True
isApp _ = False

isPi (Pi _ _ _ _) = True
isPi _ = False

pprint :: Term a -> String
pprint (Type _) = "Type"
pprint (Pi _ (Just n) τ t) = "(" ++ n ++ " : " ++ pprint τ ++ ") → " ++ pprint t
pprint (Pi _ Nothing τ@(Pi _ _ _ _) t) =
  "(" ++ pprint τ ++ ") → " ++ pprint t
pprint (Pi _ Nothing τ t) =
  pprint τ ++ " → " ++ pprint t
pprint (Var _ n) = n
pprint (Lam _ (Just n) t) = "(λ" ++ n ++ " " ++ pprint t ++ ")"
pprint (Lam _ Nothing t) = "(λ_ " ++ pprint t ++ ")"
pprint (App _ t1 t2) =
  pprintParIf isPi t1 ++ " " ++ pprintParIf (liftM2 (||) isApp isPi) t2
pprint (Let _ (Just n) t1 t2) =
  "let " ++ n ++ " = " ++ pprint t1 ++ " in " ++ pprint t2
pprint (Let _ Nothing t1 t2) = "let _ = " ++ pprint t1 ++ " in " ++ pprint t2
pprint (Annot _ t τ) = "(" ++ pprint t ++ " @ " ++ pprint τ ++ ")"
pprint (Hole _) = "?"

parseTerm :: String -> Term ()
parseTerm = parse . scanTokens

}
