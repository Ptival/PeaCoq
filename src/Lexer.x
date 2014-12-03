{
{-# OPTIONS_GHC -w #-}
module Lexer where

import Data.Char (chr)
}

%wrapper "monad"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
  ($white|\160)+ ;
  $digit+       { tokS TokNum }
  \(\*          { nestedComment }
  \(            { tok TokLParen }
  \)            { tok TokRParen }
  \{            { tok TokLBrace }
  \}            { tok TokRBrace }
  (\∀|"forall") { tok TokForall }
  (\→|\-\>)     { tok TokArrow }
  (\=\>)        { tok TokDoubleArrow }
  (\λ|\\)       { tok TokLambda }
  \.            { tok TokPeriod }
  \:\=          { tok TokColonEq }
  \:            { tok TokColon }
  \:\:          { tok TokCons }
  \[\]          { tok TokNil }
  \=            { tok TokEq }
  \≠            { tok TokNeq }
  \_            { tok TokUnderscore }
  \,            { tok TokComma }
  \+            { tok TokPlus }
  \-            { tok TokMinus }
  \*            { tok TokStar }
  \∧            { tok TokAnd }
  \/\\          { tok TokAnd }
  \∨            { tok TokOr }
  \\\/          { tok TokOr }
  \&\&          { tok TokAndB }
  \|            { tok TokPipe }
  \|\|          { tok TokOrB }
  \%            { tok TokPercent }
  \+\+          { tok TokAppend }
  "match"       { tok TokMatch }
  "with"        { tok TokWith }
  "end"         { tok TokEnd }
  "Inductive"   { tok TokInductive }
  "Theorem"     { tok TokTheorem }
  "Definition"  { tok TokDefinition }
  "Fixpoint"    { tok TokFixpoint }
  "Check"       { tok TokCheck }
  "struct"      { tok TokStruct }
  "Proof"       { tok TokProof }
  "Qed"         { tok TokQed }
  $alpha [$alpha $digit \_ \']* { tokS TokSym }

{

tok :: Token -> AlexInput -> Int -> Alex Token
tok t _ _ = return t

tokS :: (String -> Token) -> AlexInput -> Int -> Alex Token
tokS t (_, _, _, str) len = return (t (take len str))

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
  | TokAppend
  | TokNum String
  | TokMatch
  | TokWith
  | TokEnd
  | TokInductive
  | TokTheorem
  | TokDefinition
  | TokFixpoint
  | TokCheck
  | TokStruct
  | TokProof
  | TokQed
  | TokComment String
  | TokEOF
  deriving (Eq,Show)

lexWrap :: (Token -> Alex a) -> Alex a
lexWrap cont = do
    tok <- alexMonadScan
    cont tok

nestedComment :: AlexInput -> Int -> Alex Token
nestedComment _ _ = do
  input <- alexGetInput
  go 1 input "(*"
    where
      liftM f m1 = do { x1 <- m1; return (f x1) }
      byte2char = chr . fromIntegral
      go 0 input res = do alexSetInput input; return (TokComment res)
      go n input res = do
        case alexGetByte input of
          Nothing -> err input
          Just (c,input) -> do
            case  byte2char c of
              '*' -> do
                case alexGetByte input of
                  Nothing -> err input
                  Just (c,input) | c == fromIntegral (ord ')') -> go (n-1) input (res ++ "*)")
                  Just (c,input) -> go n input (res ++ ['*', byte2char c])
              '(' -> do
                case alexGetByte input of
                  Nothing  -> err input
                  Just (c,input) | c == fromIntegral (ord '*') -> go (n+1) input (res ++ "(*")
                  Just (c,input) -> go n input (res ++ ['(', byte2char c])
              c -> go n input (res ++ [c])
      err input = do alexSetInput input; lexError " error in nested comment"

getPos :: AlexPosn -> (Int, Int)
getPos (AlexPn _ line column) = (line, column)

infixl 4 <$>
(<$>) :: (a -> b) -> Alex a -> Alex b
f <$> a = do
    v <- a
    return $ f v

getPosition :: Alex (Int, Int)
getPosition = Alex $ \s -> Right (s, getPos . alex_pos $ s)

lexError s = do
  (p,c,_,input) <- alexGetInput
  alexError (showPosn p ++ ": " ++ s ++
		   (if (not (null input))
		     then " before " ++ show (head input)
		     else " at end of file"))

alexEOF = return TokEOF

showPosn (AlexPn _ line col) = show line ++ ':': show col

alexScanTokens :: String -> Either String [Token]
alexScanTokens input = runAlex input gather
  where
  gather = do
    t <- alexMonadScan
    case t of
      TokEOF -> return [TokEOF]
      _      -> (t :) <$> gather

}
