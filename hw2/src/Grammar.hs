module Grammar where

import Data.List (intercalate)


data Expr = Var String    |
            Neg Expr      | 
            And Expr Expr |
            Or Expr Expr  |
            Impl Expr Expr 
            deriving (Eq, Ord) 


instance Show Expr where
  show (Var x) = x
  show (Neg e) = "!" ++ show e 
  show (And e1 e2) = "(" ++ show e1 ++ " & " ++ show e2 ++ ")"
  show (Or e1 e2) = "(" ++ show e1 ++ " | " ++ show e2 ++ ")"
  show (Impl e1 e2) = "(" ++ show e1 ++ " -> " ++ show e2 ++ ")"

