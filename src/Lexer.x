{
{-# OPTIONS_GHC -w #-}
module Lexer where
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
  ($white|\160)+ ;
  $digit+       { \s -> TokNum s }
  \(            { \s -> TokLParen }
  \)            { \s -> TokRParen }
  \{            { \s -> TokLBrace }
  \}            { \s -> TokRBrace }
  (\∀|"forall") { \s -> TokForall }
  (\→|\-\>)     { \s -> TokArrow }
  (\=\>)        { \s -> TokDoubleArrow }
  (\λ|\\)       { \s -> TokLambda }
  \.            { \s -> TokPeriod }
  \:\=          { \s -> TokColonEq }
  \:            { \s -> TokColon }
  \:\:          { \s -> TokCons }
  \[\]          { \s -> TokNil }
  \=            { \s -> TokEq }
  \≠            { \s -> TokNeq }
  \_            { \s -> TokUnderscore }
  \,            { \s -> TokComma }
  \+            { \s -> TokPlus }
  \-            { \s -> TokMinus }
  \*            { \s -> TokStar }
  \∧            { \s -> TokAnd }
  \/\\          { \s -> TokAnd }
  \∨            { \s -> TokOr }
  \\\/          { \s -> TokOr }
  \&\&          { \s -> TokAndB }
  \|            { \s -> TokPipe }
  \|\|          { \s -> TokOrB }
  \%            { \s -> TokPercent }
  "match"       { \s -> TokMatch }
  "with"        { \s -> TokWith }
  "end"         { \s -> TokEnd }
  "Inductive"   { \s -> TokInductive }
  "Theorem"     { \s -> TokTheorem }
  "Definition"  { \s -> TokDefinition }
  "Fixpoint"    { \s -> TokFixpoint }
  "struct"      { \s -> TokStruct }
  "Proof"       { \s -> TokProof }
  "Qed"         { \s -> TokQed }
  $alpha [$alpha $digit \_ \']* { \s -> TokSym s }

{

data Token
  = TokSym String
  | TokLParen
  | TokRParen
  | TokLBrace
  | TokRBrace
  | TokArrow
  | TokDoubleArrow
  | TokForall
  | TokLambda
  | TokPeriod
  | TokColon
  | TokColonEq
  | TokCons
  | TokNil
  | TokEq
  | TokNeq
  | TokUnderscore
  | TokComma
  | TokPlus
  | TokMinus
  | TokStar
  | TokPipe
  | TokAnd
  | TokOr
  | TokAndB
  | TokOrB
  | TokPercent
  | TokNum String
  | TokMatch
  | TokWith
  | TokEnd
  | TokInductive
  | TokTheorem
  | TokDefinition
  | TokFixpoint
  | TokStruct
  | TokProof
  | TokQed
  deriving (Eq,Show)

scanTokens = alexScanTokens

}
