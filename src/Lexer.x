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
  \_            { \s -> TokUnderscore }
  \,            { \s -> TokComma }
  \+            { \s -> TokPlus }
  \-            { \s -> TokMinus }
  \*            { \s -> TokStar }
  \&\&          { \s -> TokAndB }
  \|            { \s -> TokPipe }
  \|\|          { \s -> TokOrB }
  \%            { \s -> TokPercent }
  "Inductive"   { \s -> TokInductive }
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
  | TokUnderscore
  | TokComma
  | TokPlus
  | TokMinus
  | TokStar
  | TokPipe
  | TokAndB
  | TokOrB
  | TokPercent
  | TokNum String
  | TokInductive
  | TokProof
  | TokQed
  deriving (Eq,Show)

scanTokens = alexScanTokens

}
