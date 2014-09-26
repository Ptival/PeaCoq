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
  (\∀|"forall") { \s -> TokForall }
  (\→|\-\>)     { \s -> TokArrow }
  (\λ|\\)       { \s -> TokLambda }
  \.            { \s -> TokPeriod }
  \:\=          { \s -> TokColonEq }
  \:            { \s -> TokColon }
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
  "Inductive"   { \s -> TokInductive }
  "Theorem"     { \s -> TokTheorem }
  "Proof"       { \s -> TokProof }
  "Qed"         { \s -> TokQed }
  $alpha [$alpha $digit \_ \']* { \s -> TokSym s }

{

data Token
  = TokSym String
  | TokLParen
  | TokRParen
  | TokArrow
  | TokForall
  | TokLambda
  | TokPeriod
  | TokColon
  | TokColonEq
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
  | TokInductive
  | TokTheorem
  | TokProof
  | TokQed
  deriving (Eq,Show)

scanTokens = alexScanTokens

}
