{-# LANGUAGE GADTs, FlexibleContexts #-}

-- Imports for Parsec
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Token

-- AST Definition

data TABE where
  TNum :: TABE
  TBool :: TABE
  deriving (Show,Eq)

data ABE where
  Num :: Int -> ABE
  Plus :: ABE -> ABE -> ABE
  Minus :: ABE -> ABE -> ABE
  Mult :: ABE -> ABE -> ABE
  Div :: ABE -> ABE -> ABE
  Boolean :: Bool -> ABE
  And :: ABE -> ABE -> ABE
  Leq :: ABE -> ABE -> ABE
  IsZero :: ABE -> ABE
  If :: ABE -> ABE -> ABE -> ABE
  deriving (Show,Eq)

-- AST Pretty Printer

pprint :: ABE -> String
pprint (Num n) = show n
pprint (Boolean b) = show b
pprint (Plus n m) = "(" ++ pprint n ++ " + " ++ pprint m ++ ")"
pprint (Minus n m) = "(" ++ pprint n ++ " - " ++ pprint m ++ ")"
pprint (Mult n m) = "(" ++ pprint n ++ " * " ++ pprint m ++ ")"
pprint (Div n m) = "(" ++ pprint n ++ " / " ++ pprint m ++ ")"
pprint (And n m) = "(" ++ pprint n ++ " && " ++ pprint m ++ ")"
pprint (Leq n m) = "(" ++ pprint n ++ " <= " ++ pprint m ++ ")"
pprint (IsZero m) = "(isZero " ++ pprint m ++ ")"
pprint (If c n m) = "(if " ++ pprint c ++ " then " ++ pprint n ++ " else " ++ pprint m ++ ")"


-- Parser (Requires ParserUtils and Parsec)

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

expr :: Parser ABE
expr = buildExpressionParser opTable term

opTable = [ [ inFix "*" Plus AssocLeft
            , inFix "/" Minus AssocLeft ]
          , [ inFix "+" Plus AssocLeft
            , inFix "-" Minus AssocLeft ]
          , [ inFix "<=" Leq AssocLeft
            , preFix "isZero" IsZero ]
          , [ inFix "&&" And AssocLeft ]
          ]

numExpr :: Parser ABE
numExpr = do i <- integer lexer
             return (Num (fromInteger i))

trueExpr :: Parser ABE
trueExpr = do i <- reserved lexer "true"
              return (Boolean True)

falseExpr :: Parser ABE
falseExpr = do i <- reserved lexer "false"
               return (Boolean False)

ifExpr :: Parser ABE
ifExpr = do reserved lexer "if"
            c <- expr
            reserved lexer "then"
            t <- expr
            reserved lexer "else"
            e <- expr
            return (If c t e)

term = parens lexer expr
       <|> numExpr
       <|> trueExpr
       <|> falseExpr
       <|> ifExpr

-- Parser invocation

parseABE = parseString expr




---------------------------------------------------------
---------------------------------------------------------
-- Evaluation Functions
---------------------------------------------------------
---------------------------------------------------------
---------------------------------------------------------
--evalM
---------------------------------------------------------
evalM :: ABE -> (Maybe ABE)
evalM (Num a) = Just (Num a)
evalM (Boolean b) = Just (Boolean b)
evalM (Plus l r) = 
   do { x <- evalM l;
        y <- evalM r;
        return (liftNum (+) x y)
   }
evalM (Minus l r) =
   do { x <- evalM l;
        y <- evalM r;
        if ((Leq x y) == (Boolean True)) then Nothing else return (liftNum (-) x y)
   }
evalM (Mult l r) =
   do { x <- evalM l;
        y <- evalM r;
        return (liftNum (*) x y)
   }
evalM (Div l r) = 
   do { x <- evalM l;
        y <- evalM r;
        if ((IsZero y) == (Boolean True)) then Nothing else return (liftNum (div) x y)
   }
   
evalM (And l r) = 
    do {
        x <- evalM l;
        y <- evalM r;
        return (liftBool (&&) x y)
    }
evalM (Leq l r) = 
    do {
        x <- (evalM l);
        y <- (evalM r);
        return (liftBool (<=) l r)
    }
evalM (IsZero a) = 
    do { 
        x <- (evalM a);
        return (liftBool (==) x (Num 0)) 
    }
evalM (If c t e) = 
   do { x <- evalM c;
        y <- evalM t;
        z <- evalM e;
        if x == (Boolean True) then (evalM t) else (evalM e)
   }

---------------------------------------------------------
--evalErr
---------------------------------------------------------
evalErr :: ABE -> (Maybe ABE)
evalErr (Num a) = Just (Num a)
evalErr (Boolean b) = Just (Boolean b)
evalErr (Plus l r) = 
   do {
    x <- evalErr l;
    y <- evalErr r;
    case x of
        (Num a) -> case y of
            (Num b) -> Just (Num (a + b));
            _ -> Nothing;
        _ -> Nothing
    }
evalErr (Minus l r) =
   do { 
    x <- evalErr l;
    y <- evalErr r;
    case x of
        (Num a) -> case y of
            (Num b) -> if (a < b) then Nothing else (Just (Num (a - b)));
            _ -> Nothing;
        _ -> Nothing
    }
evalErr (Mult l r) =
   do { 
    x <- evalErr l;
    y <- evalErr r;
    case x of
        (Num a) -> case y of
            (Num b) -> Just (Num (a * b));
            _ -> Nothing;
        _ -> Nothing
    }
evalErr (Div l r) = 
   do {
    x <- evalErr l;
    y <- evalErr r;
    case x of
        (Num a) -> case y of
            (Num b) -> if (b == 0) then Nothing else Just (Num (div a b));   --NOTE: Might need to use IsZero
            _ -> Nothing;
        _ -> Nothing
    }
evalErr (And l r) = 
    do { 
     x <- evalErr l;
     y <- evalErr r;
    case x of
        (Boolean a) -> case y of
            (Boolean b) -> Just (Boolean (a && b));
            _ -> Nothing;
        _ -> Nothing
    }
evalErr (Leq l r) = 
    do { 
     x <- evalErr l;
     y <- evalErr r;
     case x of
        (Num a) -> case y of
            (Num b) -> Just (Boolean (a <= b));
            _ -> Nothing;
        _ -> Nothing
    }
evalErr (IsZero a) = 
    do {
     x <- evalErr a;
     case x of 
        (Num x') -> if (x' == 0) then return (Boolean True) else return (Boolean False)
    }
evalErr (If c t e) = 
   do { 
    x <- evalErr c;
    case x of
        (Boolean a) -> if a then (evalErr t) else (evalErr e);
        _ -> Nothing
    }

-- Type Derivation Function
typeofM :: ABE -> Maybe TABE
typeofM (Num _) = Just TNum
typeofM (Boolean _) = Just TBool
typeofM (Plus l r) = do {
    x <- typeofM l;
    y <- typeofM r;
    if ((x == TNum) && (y == TNum)) then (Just TNum) else Nothing 
}
typeofM (Minus l r) = do {
    x <- typeofM l;
    y <- typeofM r;
    if ((x == TNum) && (y == TNum)) then (Just TNum) else Nothing 
}
typeofM (Mult l r) = do {
    x <- typeofM l;
    y <- typeofM r;
    if ((x == TNum) && (y == TNum)) then (Just TNum) else Nothing 
}
typeofM (Div l r) = do {
    x <- typeofM l;
    y <- typeofM r;
    if ((x == TNum) && (y == TNum)) then (Just TNum) else Nothing 
}
typeofM (And l r) = do {
    x <- typeofM l;
    y <- typeofM r;
    if ((x == TBool) && (y == TBool)) then (Just TBool) else Nothing 
}
typeofM (If c t e) = do {
    tc <- typeofM c;
    tt <- typeofM t;
    te <- typeofM e;
    if (tc == TBool) then (if (tt == te) then (Just tt) else Nothing)
                     else Nothing
}
typeofM (Leq l r ) = do {
    x <- typeofM l;
    y <- typeofM r;
    if ((x == TNum) && (y == TNum)) then (Just TBool) else Nothing
}
typeOfM (IsZero x) = do {
    x' <- typeofM x;
    if (x' == TNum) then (Just TBool) else Nothing
}

-- Combined interpreter
evalTypeM :: ABE -> Maybe ABE
evalTypeM e = do {
    t <- (typeofM e);
    evalM e
}

-- Optimizer
optimize :: ABE -> ABE
optimize (Num a) = (Num a)
optimize (Boolean b) = (Boolean b)
optimize (Plus x (Num 0)) = (optimize x)
optimize (Plus x y) = (Plus (optimize x) (optimize y))
optimize (If (Boolean True) t e) = t
optimize (If (Boolean False) t e) = e
optimize (Minus a b) = (Minus (optimize a) (optimize b))
optimize (Mult a b) = (Mult (optimize a) (optimize b))
optimize (Div a b) = (Div (optimize a) (optimize b))
optimize (If c t e) = (If (optimize c) (optimize t) (optimize e))
optimize (And a b) = (And (optimize a) (optimize b))
optimize (Leq a b) = (Leq (optimize a) (optimize b))
optimize (IsZero a) = (IsZero (optimize a))

--COMBINED INTERPRETER AND Optimizer
interpOptM :: ABE -> Maybe ABE
interpOptM e = evalM (optimize e)

--LiftNum Function
liftNum :: (Int -> Int -> Int) -> ABE -> ABE -> ABE
liftNum f (Num x) (Num y) = (Num (f x y))

--LiftBool Function
liftBool :: (Bool -> Bool -> Bool) -> ABE -> ABE -> ABE
liftBool f (Boolean x) (Boolean y) = (Boolean (f x y))

--TEST CASES
tests = [(Num 0),
         (Plus (Num 3) (Num 5)),
         (Minus (Num 5) (Num 2)),
         (Minus (Num 2) (Num 5)),
         (Div (Num 0) (Num 5)),
         (Div (Num 5) (Num 0)),
         (Mult (Num 4) (Num 9)),
         (Mult (Plus (Num 3) (Num 2)) (Minus (Num 5) (Num 4))),
         (Mult (Plus (Num 7) (Num 4)) (Minus (Num 8) (Num 3))),
         (Mult (Plus (Num 6) (Num 8)) (Minus (Num 32) (Num 21)))
        ]

--TEST SIGNATURES
testM = map evalM tests
testErr = map evalErr tests
testTypeM = map evalTypeM tests
testOptM = map interpOptM tests