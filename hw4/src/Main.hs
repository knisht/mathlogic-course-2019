module Main where


import ParseModule 
import Grammar
import Data.Map.Strict
import Data.List
import Data.List.Split
import Completeness
import System.IO (isEOF)


fromJust :: Maybe a -> a
fromJust (Just a) = a
fromJust _ = undefined


isNothing :: Maybe a -> Bool
isNothing (Nothing) = True
isNothing _ = False

pretty_print :: [Expr] -> IO ()
pretty_print (e:tl) = do
    putStrLn (show e)
    pretty_print tl 
pretty_print []  = do return ()

showHyp :: Hyp -> String
showHyp h = case h of 
              Id x -> show (Var x)
              No x -> show (Neg (Var x)) 

printSmile :: IO ()
printSmile = do
  putStrLn ":("

doProof :: (Expr, [Hyp]) -> IO ()
doProof (expr, hyps) = do
  let proof = proveExpression expr hyps
  --let proof = (\(x, _) -> x) <$> generateProof expr hyps
  let header = (intercalate ", " (showHyp <$> hyps)) ++ "|- " ++ (show expr)
  putStrLn header
  pretty_print proof


main :: IO ()
main = do 
    --hypraw <- getLine
    --let context = Data.List.Split.splitOn ", " hypraw
    --let hypsraw = (Data.List.filter (\x -> length x > 0) context)
    contents <- getLine 
    if (length contents == 0) 
      then do putStrLn ":("
      else do
             let expr = getExpr contents
             let resolve = resolveHypset expr
    --let resolve = Just(expr, toHyps hypsraw (getDifferentVariables expr))
             if (isNothing resolve) then printSmile else doProof (fromJust resolve)
