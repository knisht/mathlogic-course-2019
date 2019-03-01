module Main where

import Grammar (Expr (..))
import Lexer (alexScanTokens)
import Parser (parseExpr)

main :: IO ()
main = do
  input <- getContents
  case parseExpr (alexScanTokens input) of
    Left err   -> putStrLn err
    Right expr -> putStrLn $ show expr
