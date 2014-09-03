{
module Lexer where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
  ($white|\160)+                ;
  "match"                       { \s -> TokMatch }
  "as"                          { \s -> TokAs }
  "in"                          { \s -> TokIn }
  "return"                      { \s -> TokReturn }
  "with"                        { \s -> TokWith }
  "let"                         { \s -> TokLet }
  $digit+                       { \s -> TokInt (read s) }
  \(                            { \s -> TokLParen }
  \)                            { \s -> TokRParen }
  (\∀|"forall")                 { \s -> TokForall }
  (\→|\-\>)                     { \s -> TokArrow }
  (\λ|\\)                       { \s -> TokLambda }
  \:                            { \s -> TokColon }
  \@                            { \s -> TokAnnot }
  \=                            { \s -> TokEq }
  \_                            { \s -> TokUnderscore }
  \?                            { \s -> TokHole }
  "Type"                        { \s -> TokType }
  $alpha [$alpha $digit \_ \']* { \s -> TokSym s }

{

data Token
  = TokSym String
  | TokLParen
  | TokRParen
  | TokArrow
  | TokForall
  | TokLambda
  | TokColon
  | TokAnnot
  | TokMatch
  | TokAs
  | TokIn
  | TokWith
  | TokLet
  | TokEq
  | TokUnderscore
  | TokHole
  | TokType
  | TokInt Int
  deriving (Eq,Show)

scanTokens = alexScanTokens

}
