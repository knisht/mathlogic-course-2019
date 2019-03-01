module ParseModule where
import Lexer
import Parser
import Grammar

getExpr :: String -> Expr
getExpr input = case parseExpr (alexScanTokens input) of
  Left err -> Var "error"
  Right expr -> expr

