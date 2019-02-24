module Main where

import LogicParser
import qualified Data.Text as T
import Data.Map
import Data.List
import Minimize
import System.IO (isEOF)

makeHypoMap :: [Expr] -> Map Expr Int
makeHypoMap list = hypothesesHelper 1 list

hypothesesHelper :: Int -> [Expr] -> Map Expr Int
hypothesesHelper ind (e : tl) = Data.Map.union (singleton e ind) (hypothesesHelper (ind + 1) tl)
hypothesesHelper _ [] = empty

processor :: IO Storage -> Int -> IO Storage
processor st ind = do
    done <- isEOF
    if done then 
            st 
            else do 
                 line <- getLine 
                 let expr = unwrap $ prs line
                 core_st <- st
                 new_st <- return $ putIntoComputer expr ind core_st
                 processor (return new_st) (ind + 1)


pretty_print :: [(Expr, MetaInfo)] -> Int -> IO ()
pretty_print ((e, meta):tl) ind = do
    let statement = format_meta meta ind ++ " " ++ format_expr e
    putStrLn statement
    pretty_print tl (ind + 1)
pretty_print [] 1 = do putStrLn "Proof is incorrect"
pretty_print [] _ = do return ()

collect_header :: [Expr] -> Expr -> Bool -> String
collect_header (e : tl) targ starter = 
                (if (starter) then ", " else "") ++ format_expr e ++ collect_header tl targ True
collect_header [] targ True = " |- " ++ format_expr targ
collect_header [] targ False = "|- " ++ format_expr targ


success :: Storage -> [Expr] -> Expr -> IO ()
success new_st hypotheses_raw targetExpression= do
    let proof = unwrapProof (strip new_st targetExpression)
    putStrLn (collect_header hypotheses_raw targetExpression False)
    pretty_print proof 1

faily :: IO ()
faily = do
    putStrLn "Proof is incorrect"

main :: IO ()
main = do 
    contents <- getLine 
    let datas = T.splitOn (T.pack "|-") (T.pack contents)
    let targetExpression = prs $ T.unpack $ head $ tail datas
    let context = T.unpack <$> T.splitOn (T.pack ",") (head datas)
    let hypotheses_raw = (\x -> unwrap $ prs x) <$> (Data.List.filter (\x -> length x > 0) context)
    let hypotheses = makeHypoMap $ hypotheses_raw
    st <- return $ (Store empty empty empty hypotheses []) 
    new_st <- processor (return st) 1
    if not $ check_correctness new_st then faily else success new_st hypotheses_raw (unwrap targetExpression) 

