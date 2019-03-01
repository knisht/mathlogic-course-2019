module Main where

import ParseModule 
import Grammar
import Data.Map.Strict
import Data.List
import Data.List.Split
import Minimize
import System.IO (isEOF)

makeHypoMap :: [Expr] -> Map Expr Int
makeHypoMap list = hypothesesHelper 1 list

hypothesesHelper :: Int -> [Expr] -> Map Expr Int
hypothesesHelper ind (e : tl) = Data.Map.Strict.union (singleton e ind) (hypothesesHelper (ind + 1) tl)
hypothesesHelper _ [] = empty

processor :: IO Storage -> Int -> IO Storage
processor st ind = do
    done <- isEOF
    if done then 
            st 
            else do 
                 line <- getLine 
                 if length line == 0
                    then 
                        return (Store empty empty empty empty []) 
                    else do
                        let expr = getExpr line
                        core_st <- st
                        new_st <- return $ putIntoComputer expr ind core_st
                        if isJust new_st then processor (return (fromJust new_st)) (ind+1) 
                            else
                            return (Store empty empty empty empty [])


pretty_print :: [(Expr, MetaInfo)] -> Int -> IO ()
pretty_print ((e, meta):tl) ind = do
    let statement = format_meta meta ind ++ " " ++ (show e)
    putStrLn statement
    pretty_print tl (ind + 1)
pretty_print [] 1 = do putStrLn "Proof is incorrect"
pretty_print [] _ = do return ()

collect_header :: [Expr] -> Expr -> Bool -> String
collect_header (e : tl) targ starter = 
                (if (starter) then ", " else "") ++ show e ++ collect_header tl targ True
collect_header [] targ True = " |- " ++ show targ
collect_header [] targ False = "|- " ++ show targ


needHeader :: [(Expr, MetaInfo)] -> Bool
needHeader [] = False
needHeader _ = True

success :: Storage -> [Expr] -> Expr -> IO ()
success new_st hypotheses_raw targetExpression= do
    let proof = if checklast new_st targetExpression 
                then unwrapProof (strip new_st targetExpression) targetExpression
                else []
    if needHeader proof then putStrLn (collect_header hypotheses_raw targetExpression False)     else return ()
    pretty_print proof 1

szz :: Storage -> String
szz (Store a b c d e) = show $ length e


main :: IO ()
main = do 
    contents <- getLine 
    let datas = Data.List.Split.splitOn "|-" contents
    let targetExpression = getExpr $ head $ tail datas
    let context = Data.List.Split.splitOn "," (head datas)
    let hypotheses_raw = getExpr <$> (Data.List.filter (\x -> length x > 0) context)
    let hypotheses = makeHypoMap $ hypotheses_raw
    st <- return $ (Store empty empty empty hypotheses []) 
    new_st <- processor (return st) 1
    success new_st hypotheses_raw targetExpression 

