module First where

import Control.Monad (void)
import Control.Monad.Combinators.Expr -- from parser-combinators
import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L


data Expr = Var String |
             Neg Expr | 
             And Expr Expr |
             Or Expr Expr |
             Impl Expr Expr 
             deriving (Show, Eq) 



type Parser = Parsec Void String


sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

identifier :: Parser String
identifier = (lexeme . try) ((:) <$> letterChar <*> many (alphaNumChar <|> char '\'')) 

parens :: Parser a -> Parser a
parens = between (string "(") (string ")")

literal = Var <$> identifier

expr :: Parser Expr
expr = makeExprParser term table
    where
        term = parens expr <|> literal 
        table = [[Prefix (Neg <$ string "!")],
                 [InfixL (And <$ string "&")],
                 [InfixL (Or  <$ string "|")],
                 [InfixR (Impl <$ string "->")]]





f x = 2
