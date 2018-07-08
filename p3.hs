{-# LANGUAGE GADTs,FlexibleContexts #-}

-- Imports for Monads

import Control.Monad

-- CFAE AST and Type Definitions

data CFAE where
  Num :: Int -> CFAE
  Plus :: CFAE -> CFAE -> CFAE
  Minus :: CFAE -> CFAE -> CFAE
  Lambda :: String -> CFAE -> CFAE
  App :: CFAE -> CFAE -> CFAE
  Id :: String -> CFAE
  If0 :: CFAE -> CFAE -> CFAE -> CFAE
  deriving (Show,Eq)

type Env = [(String,CFAE)]

evalDynCFAE :: Env -> CFAE -> (Maybe CFAE)
evalDynCFAE e (Num a) = Just (Num a)
evalDynCFAE e (Plus l r) = 
    do { (Num x) <- (evalDynCFAE e l);
        (Num y) <- (evalDynCFAE e r);
        return (Num (x + y))
    }
evalDynCFAE e (Minus l r) =
    do { (Num x) <- (evalDynCFAE e l);
       (Num y) <- (evalDynCFAE e r);
       if (x < y) then Nothing else return (Num (x - y))
    }
evalDynCFAE e (Lambda i b) = return (Lambda i b)
evalDynCFAE e (App f a) = 
    do { 
        (Lambda i b) <- (evalDynCFAE e f);
        evalDynCFAE ((i,a):e) b
    }
evalDynCFAE e (Id i) = (lookup i e)
evalDynCFAE e (If0 c l r) = 
    do { (Num c') <- (evalDynCFAE e c);
        if (c' == 0) then (evalDynCFAE e l) else (evalDynCFAE e r)
    }

data CFAEValue where
  NumV :: Int -> CFAEValue
  ClosureV :: String -> CFAE -> Env' -> CFAEValue
  deriving (Show,Eq)

type Env' = [(String,CFAEValue)]

evalStatCFAE :: Env' -> CFAE -> (Maybe CFAEValue)
evalStatCFAE e (Num a) = Just (NumV a)
evalStatCFAE e (Plus l r) = 
    do { (NumV x) <- (evalStatCFAE e l);
        (NumV y) <- (evalStatCFAE e r);
        return (NumV (x + y))
    }
evalStatCFAE e (Minus l r) =
    do { (NumV x) <- (evalStatCFAE e l);
       (NumV y) <- (evalStatCFAE e r);
       if (x < y) then Nothing else return (NumV (x - y))
    }
evalStatCFAE e (Lambda i b) = Just (ClosureV i b e)
evalStatCFAE e (App f a) = 
    do { v <- evalStatCFAE e a;
        (ClosureV i b e') <- (evalStatCFAE e f);
        evalStatCFAE ((i,v):e') b    
    }
evalStatCFAE e (Id i) = (lookup i e)
evalStatCFAE e (If0 c l r) = 
    do { (NumV c') <- (evalStatCFAE e c);
        if (c' == 0) then (evalStatCFAE e l) else (evalStatCFAE e r)
    }

data CFBAE where
  Num' :: Int -> CFBAE
  Plus' :: CFBAE -> CFBAE -> CFBAE
  Minus' :: CFBAE -> CFBAE -> CFBAE
  Lambda' :: String -> CFBAE -> CFBAE
  App' :: CFBAE -> CFBAE -> CFBAE
  Bind' :: String -> CFBAE -> CFBAE -> CFBAE
  Id' :: String -> CFBAE
  If0' :: CFBAE -> CFBAE -> CFBAE -> CFBAE
  deriving (Show,Eq)

elabCFBAE :: CFBAE -> CFAE
elabCFBAE (Num' n) = (Num n)
elabCFBAE (Plus' l r) = (Plus (elabCFBAE l) (elabCFBAE r))
elabCFBAE (Minus' l r) = (Minus (elabCFBAE l) (elabCFBAE r))
elabCFBAE (Lambda' i b) = ((Lambda i) (elabCFBAE b))
elabCFBAE (App' f a) = (App (elabCFBAE f) (elabCFBAE a))
elabCFBAE (Bind' i v b) = (App (Lambda i (elabCFBAE b)) (elabCFBAE v))
elabCFBAE (Id' i) = (Id i)
elabCFBAE (If0' c l r) = (If0 (elabCFBAE c) (elabCFBAE l) (elabCFBAE r))

evalCFBAE :: Env' -> CFBAE -> (Maybe CFAEValue)
evalCFBAE e m = evalStatCFAE e (elabCFBAE m)


-- Test Cases

-- Note that these can be loaded separately using p3-test.hs if you do not
-- want to copy/paste into your project solution.

-- Tests for evalDynCFAE and evalDynCFAE.  test2 and test3 should demonstrate
-- the difference between static and dynamic scoping.  If you get the same
-- results with both interpreters, you've got problems.

test0=(App (Lambda "inc" (Id "inc")) (Lambda "x" (Plus (Id "x") (Num 1))))
test1=(App (Lambda "inc" (App (Id "inc") (Num 3))) (Lambda "x" (Plus (Id "x") (Num 1))))
test2=(App (Lambda "n" (App (Lambda "inc" (App (Lambda "n" (App (Id "inc") (Num 3))) (Num 3))) (Lambda "x" (Plus (Id "x") (Id "n"))))) (Num 1))
test3=(App (Lambda "Sum" (App (Id "Sum") (Num 3))) (Lambda "x" (If0 (Id "x") (Num 0) (Plus (Id "x") (App (Id "Sum") (Minus (Id "x") (Num 1)))))))

-- List of tests if you would like to use map for testing

tests = [test0,test1,test2,test3]

-- Tests for evalCFBAE and evalDynCFAE.  These are the same tests as above
-- using Bind.  You should get the same results from evalCFBAE that you
-- get from evalStateCFAE.

test0'= (Bind' "inc" (Lambda' "x" (Plus' (Id' "x") (Num' 1))) (Id' "inc"))
test1' = (Bind' "inc" (Lambda' "x" (Plus' (Id' "x") (Num' 1))) (App' (Id' "inc") (Num' 3)))
test2' = (Bind' "n" (Num' 1) (Bind' "inc" (Lambda' "x" (Plus' (Id' "x") (Id' "n"))) (Bind' "n" (Num' 3) (App' (Id' "inc") (Num' 3)))))
test3' = (Bind' "Sum" (Lambda' "x" (If0' (Id' "x") (Num' 0) (Plus' (Id' "x") (App' (Id' "Sum") (Minus' (Id' "x") (Num' 1)))))) (App' (Id' "Sum") (Num' 3)))

-- List of tests if you would like to use map for testing

tests' = [test0',test1',test2',test3']


