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

%name unsafeParseVernac      Sentence
%name unsafeParseTerm        Term
%name unsafeParseHypothesis  Hypothesis
%name unsafeParseEvalResult  EvalResult
%name unsafeParseCheckResult CheckResult
%tokentype { Token }
%lexer { lexWrap } { TokEOF }
%monad { Alex }
%error { parseError }

%token

var { TokId $$ }
num { TokNum $$ }
access_ident { TokAccessId $$ }
str { TokString $$ }
comment { TokComment $$ }
'(' { TokLParen }
')' { TokRParen }
'{' { TokLBrace }
'}' { TokRBrace }
'→' { TokArrow }
"=>" { TokDoubleArrow }
"<->" { TokEquiv }
'∀' { TokForall }
'∃' { TokExists }
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
'¬' { TokNeg }
'<' { TokLt }
'>' { TokGt }
"<=" { TokLe }
">=" { TokGe }
"&&" { TokAndB }
"||" { TokOrB }
":=" { TokColonEq }
"::" { TokCons }
"[]" { TokNil }
"++" { TokAppend }
"match" { TokMatch }
"as" { TokAs }
"in" { TokIn }
"return" { TokReturn }
"with" { TokWith }
"end" { TokEnd }
"fun" { TokFun }
"let" { TokLet }
"Inductive" { TokInductive }
"Theorem" { TokTheorem }
"Lemma" { TokLemma }
"Definition" { TokDefinition }
"Fixpoint" { TokFixpoint }
"Check" { TokCheck }
"struct" { TokStruct }
"Proof" { TokProof }
"Qed" { TokQed }

-- low precedence
%left "<->"
%right '→'
%right '∨'
%right '∧'
%nonassoc '¬'
%nonassoc '=' '≠'
%right "::"
%right "++"
%left "||"
%left "&&"
%nonassoc '<' '>' "<=" ">="
%left '+' '-'
%left '*'
%nonassoc '(' ')'
%nonassoc '{' '}'
%nonassoc var num str "[]" '∀' '∃' 'λ' '¬' "fun" "match" "let"
-- it is important that APP has higher precedence than var, num, '('
-- and all terminals that can be the start of a term,
-- so that shift/reduce conflicts of the form
-- Term Term . <var/num/'('/...>
-- gets resolved into a reduce rather than shifting the incoming token
%nonassoc APP
-- high precedence

%%

Sentence :: { Vernac }
: "Inductive" var ':' Term ":=" Constructors '.' { Inductive $2 $4 $6 }
| "Theorem" var ':' Term '.' { Theorem $2 $4 }
| "Lemma" var ':' Term '.' { Lemma $2 $4 }
| "Definition" var MaybeBinders MaybeTypeAnnotation ":=" Term '.'
  { Definition $2 $3 $4 $6 }
| "Fixpoint" var Binders MaybeAnnotation MaybeTypeAnnotation ":=" Term '.'
  { Fixpoint $2 $3 $4 $5 $7 }
| "Check" Term '.' { Check $2 }

Term :: { Term }
: QualId                  { Var $1 }
| num                     { Var $1 }
| str                     { Var $1 }
| '∀' Binders ',' Term    { Forall $2 $4 }
| 'λ' Binders ',' Term    { Lambda $2 $4 }
| "fun" Binders "=>" Term { Lambda $2 $4 }
| '∃' Binders ',' Term    { Exists $2 $4 }
| Term '→' Term           { Arrow $1 $3 }
| Term "<->" Term         { App (App (Var "iff")  $1) $3 }
| Term '=' Term           { App (App (Var "eq") $1) $3 }
| Term '≠' Term           { App (Var "not") (App (App (Var "eq") $1) $3) }
| Term '+' Term           { App (App (Var "plus")  $1) $3 }
| Term '-' Term           { App (App (Var "minus") $1) $3 }
| Term '*' Term           { App (App (Var "mult")  $1) $3 }
| Term '∧' Term           { App (App (Var "and")   $1) $3 }
| Term '∨' Term           { App (App (Var "or")    $1) $3 }
| '¬' Term                { App (Var "neg") $2 }
| Term '<' Term           { App (App (Var "lt")    $1) $3 }
| Term '>' Term           { App (App (Var "gt")    $1) $3 }
| Term "<=" Term          { App (App (Var "le")    $1) $3 }
| Term ">=" Term          { App (App (Var "ge")    $1) $3 }
| Term "&&" Term          { App (App (Var "andb")  $1) $3 }
| Term "||" Term          { App (App (Var "orb")   $1) $3 }
| Term "::" Term          { App (App (Var "cons")  $1) $3 }
| Term "++" Term          { App (App (Var "app")   $1) $3 }
| "[]"                    { Var "nil" }
| Term '%' var            { $1 }
| Term Term %prec APP     { App $1 $2 }
| '(' Term ')'            { $2 }
| "match" MatchItems MaybeReturnType "with" MaybePipe EquationStar "end" { Match $2 $3 $6 }
| "let" var MaybeBinders MaybeTypeAnnotation ":=" Term "in" Term { Let $2 $3 $4 $6 $8 }
| "let" '(' MaybeCommaSepNames ')' MaybeDepRepType ":=" Term "in" Term { LetParen $3 $5 $7 $9 }
| '(' CommaTerms ',' Term ')' { App (App (Var "prod") $2) $4 }

CommaTerms :: { Term }
: Term                { $1 }
| CommaTerms ',' Term { App (App (Var "prod") $1) $3 }

MaybeAs :: { Maybe String }
: {- empty -} { Nothing }
| "as" var    { Just $2 }

MaybeIn :: { Maybe Term }
: {- empty -} { Nothing }
| "in" Term   { Just $2 }

ReturnType :: { Type }
: "return" Term { $2 }

MaybeReturnType :: { Maybe Type }
: {- empty -} { Nothing }
| ReturnType  { Just $1 }

MaybeDepRepType :: { Maybe DepRetType }
: {- empty -}        { Nothing }
| MaybeAs ReturnType { Just ($1, $2) }

MaybeCommaSepNames :: { [String] }
: {- empty -}   { [] }
| CommaSepNames { $1 }

CommaSepNames :: { [String] }
: var                   { [$1] }
| var ',' CommaSepNames { $1 : $3 }

QualId :: { String }
: var                 { $1 }
| QualId access_ident { $1 ++ $2 }

MatchItems :: { [MatchItem] }
: MatchItem                { [$1] }
| MatchItem ',' MatchItems { $1 : $3 }

MatchItem :: { MatchItem }
: Term MaybeAs MaybeIn { ($1, $2, $3) }

EquationStar :: { [Equation] }
: {- empty -}                          { [] }
| MaybePipe Equation PipedEquationStar { $2 : $3 }

PipedEquationStar :: { [Equation] }
: {- empty -}                    { [] }
| '|' Equation PipedEquationStar { $2 : $3 }

Equation :: { Equation }
: MultiPattern PipedMultiPatternStar "=>" Term { (($1 : $2), $4) }

PipedMultiPatternStar :: { [MultiPattern] }
: {- empty -}              { [] }
| '|' MultiPattern PipedMultiPatternStar { $2 : $3 }

MultiPattern :: { MultiPattern }
: Pattern                  { [$1] }
| Pattern ',' MultiPattern { $1 : $3 }

Pattern :: { Pattern }
: QualId PatternStar   { Pattern $1 $2 }
| Pattern "::" Pattern { Pattern "cons" [$1, $3] }
| '_'                  { Wildcard }
| num                  { Pattern $1 [] }

PatternStar :: { [Pattern] }
: {- empty -}         { [] }
| Pattern PatternStar { $1 : $2 }

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

EvalResult :: { EvalResult }
: '=' Term ':' Term { EvalResult $2 $4 }

CheckResult :: { CheckResult }
: Term ':' Term { CheckResult $1 $3 }

{

parseError :: Token -> Alex a
parseError t = do
    (line, column) <- getPosition
    alexError $ "unexpected token " ++ show t
      ++ " at line " ++ show line
      ++ ", column " ++ show (column - 1)

data Vernac
  = Inductive String Type [Constructor]
  | Theorem String Type
  | Lemma String Type
  | Definition String [Binder] (Maybe Type) Term
  | Fixpoint String [Binder] (Maybe String) (Maybe Type) Term
  | Check Term
  | Comment String
  deriving (Generic, Show)

data Constructor
  = Constructor String (Maybe Type)
  deriving (Generic, Show)

type DepRetType = (Maybe String, Type)
type MatchItem = (Term, Maybe String, Maybe Type)

data Term
  = Var String
  | Forall Binders Term
  | Lambda Binders Term
  | Exists Binders Term
  | Arrow Term Term
  | App Term Term
  | Match [MatchItem] (Maybe Type) [Equation]
  | Let String Binders (Maybe Type) Term Term
  | LetParen [String] (Maybe DepRetType) Term Term
  deriving (Eq, Generic, Show)

type Type = Term

type Binders = [Binder]

data Pattern
  = Pattern String [Pattern]
  | Wildcard
  deriving (Eq, Generic, Show)

type MultiPattern = [Pattern]

type Equation = ([MultiPattern], Term)

data Binder = MkBinder [Maybe String] (Maybe Type)
  deriving (Eq, Generic, Show)

data Hypothesis
  = MkHyp
  { hName :: String
  , hValue :: Maybe Term
  , hType :: Term
  }
  deriving (Eq, Generic, Show)

data EvalResult = EvalResult Term Type
  deriving (Generic, Show)

data CheckResult = CheckResult Term Type
  deriving (Generic, Show)

unsafeRight :: Either String b -> b
unsafeRight (Right b) = b
unsafeRight (Left e) = error e

parseVernac :: String -> Vernac
parseVernac s = unsafeRight $ runAlex s unsafeParseVernac

-- successfully parse or let the string as is
safeParse parser s = either (const (Left s)) Right (runAlex s parser)

parseTerm :: String -> Either String Term
parseTerm = safeParse unsafeParseTerm

parseHypothesis :: String -> Either String Hypothesis
parseHypothesis = safeParse unsafeParseHypothesis

parseEvalResult :: String -> EvalResult
parseEvalResult s = unsafeRight $ runAlex s unsafeParseEvalResult

parseCheckResult :: String -> CheckResult
parseCheckResult s = unsafeRight $ runAlex s unsafeParseCheckResult

instance ToJSON Vernac where
instance ToJSON Constructor where
instance ToJSON Binder where
instance ToJSON Term where
instance ToJSON Hypothesis where
instance ToJSON Pattern where
instance ToJSON EvalResult where
instance ToJSON CheckResult where

}
