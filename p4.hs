{-# LANGUAGE GADTs #-}

import Text.ParserCombinators.Parsec
import Control.Monad
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as Token

-- Calculator language extended with an environment to hold defined variables

data TFBAE where
  TNum :: TFBAE
  TBool :: TFBAE
  (:->:) :: TFBAE -> TFBAE -> TFBAE
  deriving (Show,Eq)

data FBAE where
  Num :: Int -> FBAE
  Plus :: FBAE -> FBAE -> FBAE
  Minus :: FBAE -> FBAE -> FBAE
  Mult :: FBAE -> FBAE -> FBAE
  Div :: FBAE -> FBAE -> FBAE
  Bind :: String -> FBAE -> FBAE -> FBAE
  Lambda :: String -> TFBAE -> FBAE -> FBAE
  App :: FBAE -> FBAE -> FBAE
  Id :: String -> FBAE
  Boolean :: Bool -> FBAE
  And :: FBAE -> FBAE -> FBAE
  Or :: FBAE -> FBAE -> FBAE
  Leq :: FBAE -> FBAE -> FBAE
  IsZero :: FBAE -> FBAE
  If :: FBAE -> FBAE -> FBAE -> FBAE
  Fix :: FBAE -> FBAE
  deriving (Show,Eq)

-- Value defintion for statically scoped eval

data FBAEVal where
  NumV :: Int -> FBAEVal
  BooleanV :: Bool -> FBAEVal
  ClosureV :: String -> TFBAE -> FBAE -> Env -> FBAEVal
  deriving (Show,Eq)

-- Enviornment for statically scoped eval

type Env = [(String,FBAEVal)]

-- Statically scoped eval
         
evalM :: Env -> FBAE -> (Maybe FBAEVal)
evalM e (Num a) = Just (NumV a)
evalM e (Plus l r) = 
    do { (NumV x) <- (evalM e l);
        (NumV y) <- (evalM e r);
        return (NumV (x + y))
    }
evalM e (Minus l r) =
    do { (NumV x) <- (evalM e l);
       (NumV y) <- (evalM e r);
       if (x < y) then Nothing else return (NumV (x - y))
    }
evalM e (Mult l r) = 
    do { (NumV x) <- (evalM e l);
        (NumV y) <- (evalM e r);
        return (NumV (x * y))
    }
evalM e (Div l r) =
    do { (NumV x) <- (evalM e l);
       (NumV y) <- (evalM e r);
       if ((IsZero (Num x)) == (Boolean True)) then Nothing else return (NumV (div x y))
    }
evalM e (Bind i v b) = 
    do { v' <- evalM e v;
        evalM ((i, v'):e) b
    }
evalM e (Lambda i t b) = Just (ClosureV i t b e)
evalM e (App f a) =
    do { v <- evalM e a;
        (ClosureV i t b e') <- (evalM e f);
        evalM ((i,v):e') b    
    }
evalM e (Id i) = (lookup i e)
evalM e (Boolean b) = Just (BooleanV b)
evalM e (And l r) = 
    do {
        (BooleanV x) <- evalM e l;
        (BooleanV y) <- evalM e r;
        return (BooleanV (x && y))
    }
evalM e (Or l r) = 
    do {
        (BooleanV x) <- evalM e l;
        (BooleanV y) <- evalM e r;
        return (BooleanV (x || y))
    }
evalM e (Leq l r) = 
    do {
        (NumV x) <- (evalM e l);
        (NumV y) <- (evalM e r);
        return (BooleanV (x <= y))
    }
evalM e (IsZero a) = 
    do { 
        (NumV x) <- (evalM e a);
        return (BooleanV (x == 0))
    }
evalM env (If c t e) = 
    do { (BooleanV x) <- evalM env c;
        if x then (evalM env t) else (evalM env e)
    }
evalM e (Fix f) = 
    do { (ClosureV i t b e') <- evalM e f;
        evalM e (subst i (Fix (Lambda i TNum b)) b)    --arbitrary type TNum
    }

-- Type inference function

type Cont = [(String,TFBAE)]

typeofM :: Cont -> FBAE -> (Maybe TFBAE)
typeofM cont (Num x) = (Just TNum)
typeofM cont (Plus l r) = 
    do { 
        l' <- (typeofM cont l);
        r' <- (typeofM cont r);
        if l'==TNum && r'==TNum
        then return TNum
        else Nothing
    }
typeofM cont (Minus l r) = 
    do { 
        l' <- (typeofM cont l);
        r' <- (typeofM cont r);
        if l'==TNum && r'==TNum
        then return TNum
        else Nothing 
    }
typeofM cont (Mult l r) = 
    do { 
        l' <- (typeofM cont l);
        r' <- (typeofM cont r);
        if l'==TNum && r'==TNum
        then return TNum
        else Nothing 
    }
typeofM cont (Div l r) = 
    do { 
        l' <- (typeofM cont l);
        r' <- (typeofM cont r);
        if l'==TNum && r'==TNum
        then return TNum
        else Nothing 
    }
typeofM cont (Bind i v b) = 
    do { 
        v' <- typeofM cont v;
        typeofM ((i,v'):cont) b 
    }
typeofM cont (Lambda x t b) = 
    do { tyB <- typeofM ((x,t):cont) b;
        return (t :->: tyB)
    }
typeofM cont (App x y) = 
    do { tyXd :->: tyXr <- typeofM cont x;
        tyY <- typeofM cont y;
        if tyXd==tyY
        then return tyXr
        else Nothing
    }
typeofM cont (Id n) = (lookup n cont)
typeofM cont (Boolean b) = Just TBool
typeofM cont (And l r) = 
    do { 
        TBool <- (typeofM cont l);
        TBool <- (typeofM cont r);
        return TBool
    }
typeofM cont (Or l r) = 
    do { 
        TBool <- (typeofM cont l);
        TBool <- (typeofM cont r);
        return TBool
    }
typeofM cont (Leq l r) = 
    do { 
        TNum <- (typeofM cont l);
        TNum <- (typeofM cont r);
        return TBool 
    }
typeofM cont (IsZero v) = 
    do { 
    TNum <- (typeofM cont v);
    return TBool
    }
typeofM cont (If c t e) = 
    do { 
        c' <- (typeofM cont c);
        t' <- (typeofM cont t);
        e' <- (typeofM cont e);
        if t'==e' then return t' else Nothing 
    }
typeofM cont (Fix t) = 
    do { (d :->: r) <- typeofM cont t ;
        return r 
    }


-- Interpreter
interp :: FBAE -> (Maybe FBAEVal)
interp e = case (typeofM [] e) of
            (Just _) -> (evalM [] e)
            Nothing  -> Nothing

-- Factorial function for testing evalM and typeofM.  the type of test1 should
-- be TNum and the result of evaluating test1`should be (NumV 6).  Remember
-- that Just is used to return both the value and type.

test1 = (Bind "f" (Lambda "g" ((:->:) TNum TNum)
                    (Lambda "x" TNum (If (IsZero (Id "x")) (Num 1)
                                         (Mult (Id "x")
                                               (App (Id "g")
                                                    (Minus (Id "x")
                                                           (Num 1)))))))
         (App (Fix (Id "f")) (Num 3)))
 
------------------------------------
--SUBST
------------------------------------
subst :: String -> FBAE -> FBAE -> FBAE
subst _ _ (Num x) = (Num x)
subst i v  (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v  (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v  (Mult l r) = (Mult (subst i v l) (subst i v r))
subst i v  (Div l r) = (Div (subst i v l) (subst i v r))
subst i v (Bind i' v' b') = if (i == i')
                            then (Bind i' (subst i v v') b')
                            else (Bind i' (subst i v v') (subst i v b'))
subst i v (Lambda i' t b) = if (i == i')
                            then (Lambda i' t b)
                            else (Lambda i' t (subst i v b))
subst i v (App f a) = (App (subst i v f) (subst i v a)) 
subst i v (Id i') = if (i == i')
                    then v
                    else (Id i')
subst _ _ (Boolean x) = (Boolean x)
subst i v  (And l r) = (And (subst i v l) (subst i v r))
subst i v  (Or l r) = (Or (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero n) = (IsZero (subst i v n))
subst i v (If c t e) = (If (subst i v c) (subst i v t) (subst i v e))
subst _ _ (Fix f) = (Fix f)
