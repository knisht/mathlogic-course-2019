module LogicParser where

import Control.Monad (void)
import Control.Monad.Combinators.Expr -- from parser-combinators
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


data Expr = Var String    |
            Neg Expr      | 
            And Expr Expr |
            Or Expr Expr  |
            Impl Expr Expr 
            deriving (Show, Eq, Ord) 



type Parser = Parsec Void String



sc :: Parser ()
sc = L.space space1 empty empty

symbol :: String -> Parser String
symbol = L.symbol sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

identifier :: Parser String
identifier = (lexeme . try) ((:) <$> letterChar <*> many (alphaNumChar <|> char '\'')) 

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

literal:: Parser Expr
literal = Var <$> identifier

manyUnaryNeg = foldr1 (.) <$> some (Neg <$ symbol "!")

expr :: Parser Expr
expr = between sc sc $ makeExprParser term table
    where
        term = parens expr <|> literal  
        table = [[Prefix (manyUnaryNeg)],
                 [InfixL (And <$ symbol "&")],
                 [InfixL (Or  <$ symbol "|")],
                 [InfixR (Impl <$ symbol "->")]]

prs :: String -> Maybe Expr
prs input = parseMaybe expr input

render :: Expr -> String
render (Var x) = x
render (Neg e) = "(!" ++ render e ++ ")"
render (And e1 e2) = "(&," ++ render e1 ++ "," ++ render e2 ++ ")"
render (Or e1 e2) = "(|," ++ render e1 ++ "," ++ render e2 ++ ")"
render (Impl e1 e2) = "(->," ++ render e1 ++ "," ++ render e2 ++ ")"


unwrap :: Maybe a -> a
unwrap (Just x) = x
unwrap (Nothing) = undefined


format_expr :: Expr -> String
format_expr (Var x) = x
format_expr (Neg e) = "!" ++ format_expr e
format_expr (And e1 e2) = "(" ++ format_expr e1 ++ " & " ++ format_expr e2 ++ ")"
format_expr (Or e1 e2) = "(" ++ format_expr e1 ++ " | " ++ format_expr e2 ++ ")"
format_expr (Impl e1 e2) = "(" ++ format_expr e1 ++ " -> " ++ format_expr e2 ++ ")"
