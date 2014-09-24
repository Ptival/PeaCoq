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
  \:            { \s -> TokColon }
  \=            { \s -> TokEq }
  \_            { \s -> TokUnderscore }
  \,            { \s -> TokComma }
  \+            { \s -> TokPlus }
  \-            { \s -> TokMinus }
  \*            { \s -> TokStar }
  \&\&          { \s -> TokAndB }
  \|\|          { \s -> TokOrB }
  \%            { \s -> TokPercent }
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
  | TokColonEq
  | TokEq
  | TokUnderscore
  | TokComma
  | TokPlus
  | TokMinus
  | TokStar
  | TokAndB
  | TokOrB
  | TokPercent
  | TokNum String
  deriving (Eq,Show)

scanTokens = alexScanTokens

}
