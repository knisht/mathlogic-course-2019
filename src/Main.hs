module Main where

import ParseExpression

main :: IO ()
main = do 
    contents <- getContents
    putStrLn $ unwrap $ render <$> prs contents
    return ()
