{-# LANGUAGE GADTs, FlexibleContexts #-}

-- Imports for QuickCheck
import System.Random
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Function
import Test.QuickCheck.Monadic

-- Imports for Parsec
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

--
-- Simple caculator over naturals with no identifiers
--
-- Author: Perry Alexander
-- Date: Tue Jan 23 17:54:44 CST 2018
--
-- Source files for the Arithmetic Expressions (AE) language from PLIH
--

-- AST Definition

data AE where
  Num :: Int -> AE
  Plus :: AE -> AE -> AE
  Minus :: AE -> AE -> AE
  Mult :: AE -> AE -> AE
  Div :: AE -> AE -> AE
  If0 :: AE -> AE -> AE -> AE
  deriving (Show,Eq)

-- AE Parser (Requires ParserUtils and Parsec included above)

languageDef =
  javaStyle { identStart = letter
            , identLetter = alphaNum
            , reservedNames = [ "if0"
                              , "then"
                              , "else"
                              ]
            , reservedOpNames = [ "+","-","*","/"]
            }
  
lexer = makeTokenParser languageDef

inFix o c a = (Infix (reservedOp lexer o >> return c) a)
preFix o c = (Prefix (reservedOp lexer o >> return c))
postFix o c = (Postfix (reservedOp lexer o >> return c))

parseString p str =
  case parse p "" str of
    Left e -> error $ show e
    Right r -> r

expr :: Parser AE
expr = buildExpressionParser operators term

operators = [
  [ inFix "*" Mult AssocLeft
    , inFix "/" Div AssocLeft ]
  , [ inFix "+" Plus AssocLeft
  , inFix "-" Minus AssocLeft ]
  ]
  
numExpr :: Parser AE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

ifExpr :: Parser AE
ifExpr  = do reserved lexer "if0"
             c <- expr
             reserved lexer "then"
             t <- expr
             reserved lexer "else"
             e <- expr
             return (If0 c t e)
                     

term = parens lexer expr
       <|> numExpr
       <|> ifExpr

-- Parser invocation
-- Call parseAE to parse a string into the AE data structure.

parseAE = parseString expr

-- Evaluation Functions
-- Replace the bodies of these functions with your implementations for
-- Exercises 1-4.  Feel free to add utility functions or testing functions as
-- you see fit, but do not change the function signatures.  Note that only
-- Exercise 4 requires you to integrate the parser above.

-- FIRST INTERPRETER 
evalAE :: AE -> Int
evalAE (Num a) = a
evalAE (Plus l r) = (evalAE l) + (evalAE r)
evalAE (Minus l r) = 
   if (evalAE l) < (evalAE r) then error "!" else (evalAE l) - (evalAE r)
evalAE (Mult l r) = (evalAE l) * (evalAE r)
evalAE (Div l r) = 
   if (evalAE r) == 0 then error "!" else (div (evalAE l) (evalAE r))
evalAE (If0 c t e) = 
   if (evalAE c == 0) then (evalAE t) else (evalAE e)

--SECOND INTERPRETER
evalAEMaybe :: AE -> Maybe Int
evalAEMaybe (Num a) = Just a
evalAEMaybe (Plus l r) = case evalAEMaybe l of 
   Just ll -> case evalAEMaybe r of
      Just rr -> Just (ll + rr);
      Nothing -> Nothing;
   Nothing -> Nothing
evalAEMaybe (Minus l r) = case evalAEMaybe l of 
   Just ll -> case evalAEMaybe r of
      Just rr -> if (ll < rr) then Nothing else (Just (ll - rr));
      Nothing -> Nothing;
   Nothing -> Nothing
evalAEMaybe (Mult l r) = case evalAEMaybe l of 
   Just ll -> case evalAEMaybe r of
      Just rr -> Just (ll * rr);
      Nothing -> Nothing;
   Nothing -> Nothing
evalAEMaybe (Div l r) = case evalAEMaybe l of 
   Just ll -> case evalAEMaybe r of
      Just rr -> Just (div ll rr);
      Nothing -> Nothing;
   Nothing -> Nothing
evalAEMaybe (If0 c t e) = case evalAEMaybe c of
   Just cc -> if cc == 0
      then case evalAEMaybe t of 
         Just tt -> Just tt;
         Nothing -> Nothing;
      else case evalAEMaybe e of 
         Just ee -> Just ee;
         Nothing -> Nothing;
   Nothing -> Nothing;
   
 --THIRD INTERPRETER
evalM :: AE -> Maybe Int
evalM (Num a) = Just a
evalM (Plus l r) = 
   do { x <- evalM l;
        y <- evalM r;
        return (x + y)
   }
evalM (Minus l r) =
   do { x <- evalM l;
        y <- evalM r;
        if (x < y) then Nothing else return (x - y)
   }
evalM (Mult l r) =
   do { x <- evalM l;
        y <- evalM r;
        return (x * y)
   }
evalM (Div l r) = 
   do { x <- evalM l;
        y <- evalM r;
        if (y == 0) then Nothing else return (div x y)
   }
evalM (If0 c t e) = 
   do { x <- evalM c;
        y <- evalM t;
        z <- evalM e;
        if x == 0 then return y else return z
   }

--PARSER
interpAE :: String -> Maybe Int
interpAE x = evalM (parseAE x)

--TEST CASES
tests = [(Num 0),
         (Plus (Num 3) (Num 5)),
         (Div (Num 0) (Num 5)),
         (Minus (Num 5) (Num 2)),
         (Mult (Num 4) (Num 9)),
         (Mult (Plus (Num 4) (Num 9)) (Minus (Num 8) (Num 3)))
        ]

--TEST SIGNATURES
testAE = map evalAE tests
testAEMaybe = map evalAEMaybe tests
testM = map evalM tests
