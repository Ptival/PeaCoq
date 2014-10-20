{
{-# LANGUAGE DeriveGeneric, DeriveDataTypeable #-}

module Parser where

import Data.Aeson
import Control.Monad
import Data.Char (isSpace, isAlpha, isDigit)
import Data.Typeable
import GHC.Generics hiding (Constructor)

import Lexer
}

%name unsafeParseVernac     Sentence
%name unsafeParseTerm       Term
%name unsafeParseHypothesis Hypothesis
%name unsafeParseEval       Eval
%tokentype { Token }
%error { parseError }

%token

var { TokSym $$ }
num { TokNum $$ }
'(' { TokLParen }
')' { TokRParen }
'{' { TokLBrace }
'}' { TokRBrace }
'→' { TokArrow }
"=>" { TokDoubleArrow }
'∀' { TokForall }
'λ' { TokLambda }
':' { TokColon }
'.' { TokPeriod }
'=' { TokEq }
'≠' { TokNeq }
'_' { TokUnderscore }
',' { TokComma }
'+' { TokPlus }
'-' { TokMinus }
'*' { TokStar }
'%' { TokPercent }
'|' { TokPipe }
'∧' { TokAnd }
'∨' { TokOr }
"&&" { TokAndB }
"||" { TokOrB }
":=" { TokColonEq }
"::" { TokCons }
"[]" { TokNil }
"++" { TokAppend }
"match" { TokMatch }
"with" { TokWith }
"end" { TokEnd }
"Inductive" { TokInductive }
"Theorem" { TokTheorem }
"Definition" { TokDefinition }
"Fixpoint" { TokFixpoint }
"struct" { TokStruct }
"Proof" { TokProof }
"Qed" { TokQed }

-- low precedence
%right '→'
%left '∧' '∨'
%nonassoc '=' '≠'
%right "++"
%right "::"
%left "&&" "||"
%left '+' '-'
%left '*'
%nonassoc '(' ')'
%nonassoc '{' '}'
%left var
-- high precedence

%%

Eval :: { Eval }
: '=' Term ':' Term { Eval $2 $4 }

Sentence :: { Vernac }
: "Inductive" var ':' Term ":=" Constructors '.' { Inductive $2 $4 $6 }
| "Theorem" var ':' Term '.' { Theorem $2 $4 }
| "Definition" var MaybeBinders MaybeTypeAnnotation ":=" Term '.'
{ Definition $2 $3 $4 $6 }
| "Fixpoint" var Binders MaybeAnnotation MaybeTypeAnnotation ":=" Term '.'
{ Fixpoint $2 $3 $4 $5 $7 }

Term :: { Term }
: var                                              { Var $1 }
| num                                              { Var $1 }
| '∀' Binders ',' Term                             { Forall $2 $4 }
| 'λ' Binders ',' Term                             { Lambda $2 $4 }
| Term '→' Term                                    { Arrow $1 $3 }
| Term '=' Term                                    { App (App (Var "eq") $1) $3 }
| Term '≠' Term                                    { App (Var "not") (App (App (Var "eq") $1) $3) }
| Term '+' Term                                    { App (App (Var "plus")  $1) $3 }
| Term '-' Term                                    { App (App (Var "minus") $1) $3 }
| Term '*' Term                                    { App (App (Var "mult")  $1) $3 }
| Term '∧' Term                                    { App (App (Var "and")   $1) $3 }
| Term '∨' Term                                    { App (App (Var "or")    $1) $3 }
| Term "&&" Term                                   { App (App (Var "andb")  $1) $3 }
| Term "||" Term                                   { App (App (Var "orb")   $1) $3 }
| Term "::" Term                                   { App (App (Var "cons")  $1) $3 }
| Term "++" Term                                   { App (App (Var "app")   $1) $3 }
| "[]"                                             { Var "nil" }
| Term '%' var                                     { $1 }
| Term Term %prec var                              { App $1 $2 }
| '(' Term ')'                                     { $2 }
| "match" Term "with" MaybePipe EquationStar "end" { Match $2 $5 }

EquationStar :: { [Equation] }
: {- empty -}                          { [] }
| MaybePipe Equation PipedEquationStar { $2 : $3 }

PipedEquationStar :: { [Equation] }
: {- empty -}                    { [] }
| '|' Equation PipedEquationStar { $2 : $3 }

Equation :: { Equation }
: Pattern PipedPatternStar "=>" Term { (($1 : $2), $4) }

PipedPatternStar :: { [Pattern] }
: {- empty -}              { [] }
| '|' Pattern PipedPatternStar { $2 : $3 }

PatternStar :: { [Pattern] }
: {- empty -}         { [] }
| Pattern PatternStar { $1 : $2 }

Pattern :: { Pattern }
: var SubpatternStar   { Pattern $1 $2 }
| Pattern "::" Pattern { Pattern "cons" [$1, $3] }
| '_'                  { Wildcard }

SubpatternStar :: { [Pattern] }
: {- empty -}                    { [] }
| var SubpatternStar             { Pattern $1 [] : $2 }
| '(' Pattern ')' SubpatternStar { $2 : $4 }

MaybePipe :: { () }
: {- empty -} { () }
| '|'         { () }

MaybeAnnotation :: { Maybe String }
: {- empty -}          { Nothing }
| '{' "struct" var '}' { Just $3 }

MaybeTypeAnnotation :: { Maybe Type }
: {- empty -} { Nothing }
| ':' Term    { Just $2 }

Constructors :: { [Constructor] }
: MoreConstructors             { $1 }
| Constructor MoreConstructors { $1 : $2 }

MoreConstructors :: { [Constructor] }
: {- empty -}                      { [] }
| '|' Constructor MoreConstructors { $2 : $3 }

Constructor :: { Constructor }
: var ':' Term { Constructor $1 (Just $3) }
| var          { Constructor $1 Nothing }

Binders :: { [Binder] }
: Binder MaybeBinders { $1 : $2 }
| Names ':' Term      { [MkBinder $1 (Just $3)] }

MaybeBinders :: { [Binder] }
: {- empty -} { [] }
| MoreBinders { $1 }

MoreBinders :: { [Binder] }
: Binder MaybeBinders { $1 : $2 }

Binder :: { Binder }
: Names                  { MkBinder $1 Nothing   }
| '(' Names ':' Term ')' { MkBinder $2 (Just $4) }

Names :: { [Maybe String] }
: Name       { [$1] }
| Name Names { $1 : $2 }

Name :: { Maybe String }
: var { Just $1 }
| '_' { Nothing }

Hypothesis :: { Hypothesis }
: var ':' Term           { MkHyp $1 Nothing $3 }
| var ":=" Term ':' Term { MkHyp $1 (Just $3) $5 }

{

parseError :: [Token] -> a
parseError l = error $ "Parse error on: " ++ show l

data Vernac
  = Inductive String Type [Constructor]
  | Theorem String Type
  | Definition String [Binder] (Maybe Type) Term
  | Fixpoint String [Binder] (Maybe String) (Maybe Type) Term
  deriving (Generic, Show)

data Constructor
  = Constructor String (Maybe Type)
  deriving (Generic, Show)

data Term
  = Var String
  | Forall Binders Term
  | Lambda Binders Term
  | Arrow Term Term
  | App Term Term
  | Match Term [Equation]
  deriving (Eq, Generic, Show)

type Type = Term

type Binders = [Binder]

data Pattern
  = Pattern String [Pattern]
  | Wildcard
  deriving (Eq, Generic, Show)

type Equation = ([Pattern], Term)

data Binder = MkBinder [Maybe String] (Maybe Type)
  deriving (Eq, Generic, Show)

data Hypothesis
  = MkHyp
  { hName :: String
  , hValue :: Maybe Term
  , hType :: Term
  }
  deriving (Eq, Generic, Show)

data Eval = Eval Term Type
  deriving (Generic, Show)

parseVernac :: String -> Vernac
parseVernac = unsafeParseVernac . scanTokens

parseTerm :: String -> Term
parseTerm = unsafeParseTerm . scanTokens

parseHypothesis :: String -> Hypothesis
parseHypothesis = unsafeParseHypothesis . scanTokens

parseEval :: String -> Eval
parseEval = unsafeParseEval . scanTokens

instance ToJSON Vernac where
instance ToJSON Constructor where
instance ToJSON Binder where
instance ToJSON Term where
instance ToJSON Hypothesis where
instance ToJSON Pattern where
instance ToJSON Eval where

}
