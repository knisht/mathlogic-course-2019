module Glivenko where

import Grammar
import Minimize(MetaInfo(..))
import Data.Map.Strict
import ParseModule(getExpr)

foo :: Int -> Int
foo x = x + 1


data DeductionMetaInfo = 
  AxiomD | ModusPonensD Expr deriving Show

glivenko_change :: [(Expr, MetaInfo)] -> [Expr]
glivenko_change array = glivenko_change_helper array 1 empty 
  where
  glivenko_change_helper :: [(Expr, MetaInfo)] -> Int -> Map Int Expr -> [Expr]
  glivenko_change_helper (head : left) ind bijected = (unwrapExpr head bijected) ++ (glivenko_change_helper left (ind + 1) (insert ind (extractFirst head) bijected))
  glivenko_change_helper []  _ _ = []


unwrapExpr :: (Expr, MetaInfo) -> Map Int Expr -> [Expr]
unwrapExpr (e, meta) collects = 
  case meta of
    Axiom i         -> unwrapAxiom e i
    ModusPonens i j -> unwrapMP e i j collects
    Hypothesis  _   -> giveDoubleNeg e


unwrapAxiom :: Expr -> Int -> [Expr]
unwrapAxiom e index = if index == 10 then unwrap10 (getLeft e) else giveDoubleNeg e 


getLeft :: Expr -> Expr
getLeft e = case e of
              Impl a b -> b
              _ -> undefined

unwrapMP :: Expr -> Int -> Int -> Map Int Expr -> [Expr]
unwrapMP e x _ mapp = substitute (mapp ! x) e undefined modusPonensFullProof  

giveDoubleNeg :: Expr -> [Expr]
giveDoubleNeg e = substitute e undefined undefined (getExpr <$> giveDoubleNegProof) 

substitute :: Expr -> Expr -> Expr -> [Expr] -> [Expr]
substitute a b c (hd : tl) = (substImmediate a b c hd) : (substitute a b c tl)
  where
  substImmediate :: Expr -> Expr -> Expr -> Expr -> Expr
  substImmediate a b c e = case e of
                             (Var name) -> substName a b c name
                             (Neg e)    -> Neg $ substImmediate a b c e
                             (And e1 e2) -> And (substImmediate a b c e1) (substImmediate a b c e2)
                             (Or e1 e2) -> Or (substImmediate a b c e1) (substImmediate a b c e2)
                             (Impl e1 e2) -> Impl (substImmediate a b c e1) (substImmediate a b c e2)
  substName :: Expr -> Expr -> Expr -> String -> Expr
  substName a b c "A" = a
  substName a b c "B" = b
  substName a b c "C" = c
  substName a b c _   = undefined
substitute _ _ _ [] = []



giveDoubleNegProof :: [String]
giveDoubleNegProof = 
  [
  "A",
  "(!A -> A) -> (!A -> !A) -> !!A",
  "A -> !A -> A",
  "!A -> A",
  "A -> !A -> !A",
  "!A -> !A",
  "(!A -> !A) -> !!A",
  "!!A"
  ]

unwrapDeduction :: Expr -> [(Expr, DeductionMetaInfo)] -> [(Expr, DeductionMetaInfo)]
unwrapDeduction hypo (hd : tl) = (unwrapDeductionHelper hypo hd) ++ unwrapDeduction hypo tl
  where
  unwrapDeductionHelper :: Expr -> (Expr, DeductionMetaInfo) -> [(Expr, DeductionMetaInfo)]
  unwrapDeductionHelper hypo (e, meta) = 
    case meta of
      AxiomD -> if e == hypo then generateAtoA e else substAxiom e hypo
      ModusPonensD origin -> substMP hypo e origin 
unwrapDeduction _ []           = [] 

generateAtoA :: Expr -> [(Expr, DeductionMetaInfo)]
generateAtoA e = zip (substitute e undefined undefined (getExpr <$> deduceAtoA)) (reparse e undefined undefined <$> metaAtoA)

deduceAtoA = 
  [
  "A -> A -> A",
  "A -> (A -> A) -> A",
  "(A -> A -> A) -> (A -> (A -> A) -> A) -> (A -> A)",
  "(A -> (A -> A) -> A) -> (A -> A)",
  "A -> A"
  ]

metaAtoA = 
  [
  AxiomD,
  AxiomD,
  AxiomD,
  ModusPonensD (getExpr "A -> A -> A"),
  ModusPonensD (getExpr "A -> (A -> A) -> A")
  ]

substAxiom :: Expr -> Expr -> [(Expr, DeductionMetaInfo)]  
substAxiom e h = zip (substitute e h undefined (getExpr <$> deduceAxiom)) (reparse e h undefined <$> axiomMeta)

reparse :: Expr -> Expr -> Expr -> DeductionMetaInfo -> DeductionMetaInfo
reparse a b c d = 
  case d of
    AxiomD -> AxiomD
    ModusPonensD e -> ModusPonensD $ head (substitute a b c [e])

deduceAxiom :: [String]
deduceAxiom = 
  [
  "A",
  "A -> B -> A",
  "B -> A"
  ]
axiomMeta = 
  [
  AxiomD,
  AxiomD,
  ModusPonensD (getExpr "A")
  ]

substMP :: Expr -> Expr -> Expr -> [(Expr, DeductionMetaInfo)]
substMP h e origin = zip (substitute h e origin (getExpr <$> deduceMP)) (reparse h e origin <$> mPMeta)

deduceMP :: [String]
deduceMP =
  [
  "(A -> C) -> ((A -> (C -> B)) -> (A -> B))",
  "(A -> (C -> B)) -> (A -> B)",
  "A -> B"
  ]

mPMeta = 
  [
  AxiomD,
  ModusPonensD (getExpr "A -> C"),
  ModusPonensD (getExpr "A -> (C -> B)")
  ]



-- !B, A -> B |- !A
theorem3 :: [(Expr, DeductionMetaInfo)]
theorem3 = 
  makeExprs <$> [
  ("!B", AxiomD),
  ("A -> B", AxiomD),
  ("!B -> A -> !B", AxiomD),
  ("A -> !B", ModusPonensD (getExpr "!B")),
  ("(A -> B) -> (A -> !B) -> !A", AxiomD),
  ("(A -> !B) -> !A", ModusPonensD (getExpr "A -> B")),
  ("!A", ModusPonensD (getExpr "A -> !B"))
  ]

-- !!A, !B |- !(A -> B)
theorem2 :: [(Expr, DeductionMetaInfo)]
theorem2 =
  (makeExprs <$> 
  [
  ("((A -> B) -> !A) -> ((A -> B) -> !!A) -> !(A -> B)", AxiomD),
  ("!B", AxiomD)
  ])
  ++
  (unwrapDeduction (getExpr "A -> B") theorem3)
  ++
  (makeExprs <$>
  [
  ("(A -> B) -> !A", ModusPonensD (getExpr "!B")), 
  ("((A -> B) -> !!A) -> !(A -> B)", ModusPonensD (getExpr "(A -> B) -> !A")),
  ("!!A -> (A -> B) -> !!A", AxiomD),
  ("!!A", AxiomD),
  ("(A -> B) -> !!A", ModusPonensD (getExpr "!!A")),
  ("!(A -> B)", ModusPonensD (getExpr "(A -> B) -> !!A"))
  ])

-- !!A, !!(A -> B) |- !!B
modusPonensFullProof :: [Expr]
modusPonensFullProof =
  extractFirst <$>
  (makeExprs <$>
  [
  ("!!A", AxiomD),
  ("!!(A -> B)", AxiomD),
  ("(!B -> !(A -> B)) -> (!B -> !!(A -> B)) -> !!B", AxiomD) 
  ])
  ++
  (unwrapDeduction (getExpr "!B") theorem2)
  ++
  (makeExprs <$>
  [
  ("(!B -> !!(A -> B)) -> !!B", ModusPonensD (getExpr "!B -> !(A -> B)")),
  ("!!(A -> B) -> !B -> !!(A -> B)", AxiomD),
  ("!B -> !!(A -> B)", ModusPonensD (getExpr "!!(A -> B)")),
  ("!!B", ModusPonensD (getExpr "!B -> !!(A -> B)"))
  ])


unwrap10 :: Expr -> [Expr]
unwrap10 e = substitute e undefined undefined unwrap10_raw 

unwrap10_raw = 
  (getExpr <$>
  [
  "A -> !!A -> A",
  "!A -> !!A -> A"
  ])
  ++ 
  (contraposition (getExpr "A") (getExpr "!!A -> A"))
  ++
  (contraposition (getExpr "!A") (getExpr "!!A -> A"))
  ++
  (getExpr <$>
  [
  "(!(!!A -> A) -> !A) -> (!(!!A -> A) -> !!A) -> !!(!!A -> A)",
  "(!(!!A -> A) -> !!A) -> !!(!!A -> A)",
  "!!(!!A -> A)"
  ])


makeExprs = (\(x, y) -> (getExpr x, y)) 
extractFirst (a, b) = a

contraposition :: Expr -> Expr -> [Expr]
contraposition a b = substitute a b undefined contrapose_raw


contrapose_raw :: [Expr]
contrapose_raw = 
  (getExpr <$>
  [
  "(A -> B) -> (A -> !B) -> !A", 
  "((A -> B) -> (A -> !B) -> !A) -> !B -> ((A -> B) -> (A -> !B) -> !A)",
  "!B -> ((A -> B) -> (A -> !B) -> !A)",
  "(A -> B) -> !B -> (A -> B)",
  "!B -> (A -> B)",
  "!B -> (A -> !B)",
  "(!B -> (A -> B)) -> (!B -> ((A -> B) -> (A -> !B) -> !A)) -> (!B -> (A -> !B) -> !A)",
  "((!B -> ((A -> B) -> (A -> !B) -> !A)) -> (!B -> (A -> !B) -> !A))",
  "!B -> (A -> !B) -> !A",
  "(!B -> A -> !B) -> (!B -> (A -> !B) -> !A) -> (!B -> !A)",
  "(!B -> (A -> !B) -> !A) -> (!B -> !A)",
  "!B -> !A"
  ]) 
