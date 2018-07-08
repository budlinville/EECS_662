{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- BBAE AST and Type Definitions

data TBBAE where
  TNum :: TBBAE
  TBool :: TBBAE
  deriving (Show,Eq)

data BBAE where
  Num :: Int -> BBAE
  Plus :: BBAE -> BBAE -> BBAE
  Minus :: BBAE -> BBAE -> BBAE
  Bind :: String -> BBAE -> BBAE -> BBAE
  Id :: String -> BBAE
  Boolean :: Bool -> BBAE
  And :: BBAE -> BBAE -> BBAE
  Leq :: BBAE -> BBAE -> BBAE
  IsZero :: BBAE -> BBAE
  If :: BBAE -> BBAE -> BBAE -> BBAE
  deriving (Show,Eq)

type Env = [(String,BBAE)]

type Cont = [(String,TBBAE)]


------------------------------------
--SUBST
------------------------------------
subst :: String -> BBAE -> BBAE -> BBAE
subst _ _ (Num x) = (Num x)
subst i v  (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v  (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (Bind i' v' b') = if (i == i')
                            then (Bind i' (subst i v v') b')
                            else (Bind i' (subst i v v') (subst i v b'))
subst i v (Id i') = if (i == i')
                    then v
                    else (Id i')

------------------------------------
--evalS
------------------------------------
evalS :: BBAE -> (Maybe BBAE)
evalS (Num a) = Just (Num a)
evalS (Plus l r) = 
   do { (Num x) <- evalS l;
        (Num y) <- evalS r;
        return (Num (x + y))
   }
evalS (Minus l r) =
   do { (Num x) <- evalS l;
        (Num y) <- evalS r;
        if ((Leq (Num x) (Num y)) == (Boolean True)) then Nothing else return (Num (x - y))
   }
evalS (Bind i v b) = do { v' <- (evalS v) ;
                        (evalS (subst i v' b)) }
evalS (Id n) = Nothing;
evalS (Boolean b) = Just (Boolean b)
evalS (And l r) = 
    do {
        (Boolean x) <- evalS l;
        (Boolean y) <- evalS r;
        return (Boolean (x && y))
    }
evalS (Leq l r) = 
    do {
        (Boolean x) <- (evalS l);
        (Boolean y) <- (evalS r);
        return (Boolean (x <= y))
    }
evalS (IsZero a) = 
    do { 
        (Num x) <- (evalS a);
        return (Boolean (x == 0))
    }
evalS (If c t e) = 
   do { x <- evalS c;
        y <- evalS t;
        z <- evalS e;
        if x == (Boolean True) then (evalS t) else (evalS e)
   }


------------------------------------
--evalM
------------------------------------
evalM :: Env -> BBAE -> (Maybe BBAE)
evalM env (Num a) = Just (Num a)
evalM env (Plus l r) = 
   do { (Num x) <- evalM env l;
        (Num y) <- evalM env r;
        return (Num (x + y))
   }
evalM env (Minus l r) =
   do { (Num x) <- evalM env l;
        (Num y) <- evalM env r;
        return (Num (x - y))
   }
evalM env (Bind i v b) = 
   do {
       v' <- evalM env v;
       evalM ((i, v'):env) b
   }
evalM env (Id n) = (lookup n env)
evalM env (Boolean b) = Just (Boolean b)
evalM env (And l r) = 
    do {
        (Boolean x) <- evalM env l;
        (Boolean y) <- evalM env r;
        return (Boolean (x && y))
    }
evalM env (Leq l r) = 
    do {
        (Boolean x) <- (evalM env l);
        (Boolean y) <- (evalM env r);
        return (Boolean (x <= y))
    }
evalM env (IsZero a) = 
    do { 
        (Num x) <- (evalM env a);
        return (Boolean (x == 0))
    }
evalM env (If c t e) = 
   do { x <- evalM env c;
        y <- evalM env t;
        z <- evalM env e;
        if x == (Boolean True) then (evalM env t) else (evalM env e)
   }
   
------------------------------------
--TESTS
------------------------------------
testBBAE :: BBAE -> Bool
testBBAE t = (evalS t == evalM [] t)

------------------------------------
--TYPE CHECKER
------------------------------------
typeofM :: Cont -> BBAE -> (Maybe TBBAE)
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
typeofM cont (Bind i v b) = 
    do { 
        v' <- typeofM cont v;
        typeofM ((i,v'):cont) b 
    }
typeofM cont (Id n) = (lookup n cont)
typeofM cont (Boolean b) = Just TBool
typeofM cont (And l r) = 
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
        t' <- (typeofM cont t) ;
        e' <- (typeofM cont e) ;
        if t'==e' then return t' else Nothing }

evalT :: BBAE -> (Maybe BBAE)
evalT e = case (typeofM [] e) of
            (Just _) -> (evalM [] e)
            Nothing -> Nothing

