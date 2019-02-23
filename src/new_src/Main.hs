module Main where

import ParseExpression

main :: IO ()
main = do 
    contents <- getContents
    putStrLn $ prs contents
    return ()
