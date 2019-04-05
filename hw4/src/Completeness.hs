module Completeness where

import Grammar
import ParseModule
import Data.List
import Data.Maybe
import DeductionTheorem
import BindingProofs


data Hyp = Id String | No String deriving (Eq, Show)


-------------------- Part 1 : evaluation utilities -----------------------
eval :: Expr -> [Hyp] -> Bool
eval expr truthtable = evalHelper expr where
  ptable = (positive truthtable)
  evalHelper :: Expr -> Bool
  evalHelper expr = case expr of
                      Var name -> name `elem` (ptable)
                      Neg (Var name) -> not $ name `elem` (ptable) 
                      Neg e    -> not $ evalHelper e
                      Or a b   -> evalHelper a || evalHelper b 
                      And a b  -> evalHelper a && evalHelper b
                      Impl a b -> (not $ evalHelper a) || evalHelper b


positive :: [Hyp] -> [String]
positive ((Id x) : left) = x : positive left
positive ((No _) : left) = positive left
positive [] = []

getDifferentVariables :: Expr -> [String]
getDifferentVariables e = nub $ getDVhelper e [] where
  getDVhelper :: Expr -> [String] -> [String]
  getDVhelper e list = case e of
                              Var name -> name : list
                              Neg e    -> (getDVhelper e []) ++ list
                              Or a b   -> (getDVhelper a []) ++ (getDVhelper b []) ++ list 
                              And a b  -> (getDVhelper a []) ++ (getDVhelper b []) ++ list 
                              Impl a b -> (getDVhelper a []) ++ (getDVhelper b []) ++ list 

hypsets :: Expr -> [[String]]
hypsets expr = (sortBy (\l1 l2 -> compare (length l1) (length l2)) 
          $ sort 
          (subsequences
          $ letters))
  where 
  letters = getDifferentVariables expr


extractNames :: [Hyp] -> [String]
extractNames = map (\h -> case h of
                            Id x -> x
                            No x -> x) 

checkGlobalTruth :: Expr -> [Hyp] -> Bool
checkGlobalTruth e hyps = and $ (eval e) <$> allsets where
  remain = (getDifferentVariables e \\ (extractNames hyps))
  allsets :: [[Hyp]]
  allsets = ((++) hyps) <$> toHyps remain <$> (subsequences remain)


toHyps :: [String] -> [String] -> [Hyp]
toHyps known actual = map (\name -> if name `elem` actual then Id name else No name) known


findMinHypSet :: Expr -> Maybe [Hyp]
findMinHypSet e = find (\x -> checkGlobalTruth e x) $ (\x -> toHyps x x) <$> hypsets e

findMinHypSetNeg :: Expr -> Maybe [Hyp]
findMinHypSetNeg e = find (\x -> checkGlobalTruth e x) $ (\x -> toHyps x []) <$> hypsets e

resolveHypset :: Expr -> Maybe (Expr, [Hyp])
resolveHypset e = if (isJust posit)
                    then Just (e, fromJust posit)
                    else if (isJust negat)
                           then Just (Neg e, fromJust negat)
                           else Nothing
  where
  posit = findMinHypSet e
  negat = findMinHypSetNeg (Neg e)

------------------------ Part 2 : proof generation utilities ----------------------------
generateProof :: Expr -> [Hyp] -> [(Expr, DeductionMetaInfo)]
generateProof target hyps = gPHelper target 
  where
  gPHelper :: Expr -> [(Expr, DeductionMetaInfo)]
  gPHelper e = 
    case e of
      Var name -> [(Var name, AxiomD)] -- as hypo
      Neg (Var name) -> [(Neg (Var name), AxiomD)] -- as hypo
      And a b  -> (gPHelper a) ++ (gPHelper b) ++ (pTTAnd a b)
      Neg (And a b) -> andChooser a b
      Or a b -> orChooser a b
      Neg (Or a b) -> (gPHelper (Neg a)) ++ (gPHelper (Neg b)) ++ (pFFOr a b)
      Neg (Impl a b) -> (gPHelper a) ++ (gPHelper (Neg b)) ++ (pTFImpl a b)
      Impl a b -> implChooser a b
      Neg (Neg e) -> (gPHelper e) ++ (pNegNeg e)
  andChooser a b = if (not bVal) 
                     then (gPHelper (Neg b)) ++ (pTFAnd a b)
                     else (gPHelper (Neg a)) ++ (pFTAnd a b)
    where
    bVal = eval b hyps
  orChooser a b = if (aVal)
                    then (gPHelper a) ++ (pTTOr a b)
                    else (gPHelper b) ++ (pFTOr a b)
    where
    aVal = eval a hyps
  implChooser a b = if (not aVal)
                      then (gPHelper (Neg a)) ++ (pFTImpl a b)
                      else (gPHelper a) ++ (gPHelper b) ++ (pTTImpl a b)
    where
    aVal = eval a hyps


---------------------- Part 3: merging -----------------------------



mergeProofs :: [(Expr, DeductionMetaInfo)] -> [(Expr, DeductionMetaInfo)] -> String -> Expr -> [(Expr, DeductionMetaInfo)]
mergeProofs prpos prneg letter result = 
  (unwrapDeduction (Var letter) prpos)
  ++
  (unwrapDeduction (Neg (Var letter)) prneg)
  ++ 
  (substituteHelper (Var letter) result undefined <$> ((mapToExprTuple <$> ([
  ("(A -> B) -> (!A -> B) -> (A|!A -> B)", AxiomD),
  ("(!A -> B) -> (A|!A -> B)", ModusPonensD (getExpr "A -> B")),
  ("(A|!A -> B)", ModusPonensD (getExpr "!A -> B"))
  ]))
  ++
  (disjunctedThird (getExpr "A"))
  ++
  (mapToExprTuple <$> [
  ("B", ModusPonensD (getExpr "A|!A"))
  ])))


---------------------- Part 4: All together -----------------------------

proveExpression :: Expr -> [Hyp] -> [Expr]
proveExpression e hyps = (\(x, _) -> x) <$> proof 
  where
  vars = getDifferentVariables e
  remain = vars \\ extractNames hyps
  proof = proveHelper e hyps remain


proveHelper :: Expr -> [Hyp] -> [String] -> [(Expr, DeductionMetaInfo)]
proveHelper e hyps [] = generateProof e hyps
proveHelper e hyps (name : names) = 
  mergeProofs (proveHelper e ((Id name) : hyps) names)
              (proveHelper e ((No name) : hyps) names)
              name
              e
