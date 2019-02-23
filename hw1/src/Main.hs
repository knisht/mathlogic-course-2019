module Main where

import LogicParser

main :: IO ()
main = do 
    contents <- getContents
    putStrLn $ unwrap $ render <$> prs contents
    return ()
