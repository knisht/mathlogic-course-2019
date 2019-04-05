module DeductionTheorem where

import ParseModule
import Grammar

data DeductionMetaInfo = 
  AxiomD | ModusPonensD Expr deriving Show



substituteOne :: Expr -> Expr -> Expr -> Expr -> Expr
substituteOne a b c e = case e of
                          (Var name) -> substName a b c name
                          (Neg e)    -> Neg $ substituteOne a b c e
                          (And e1 e2) -> And (substituteOne a b c e1) (substituteOne a b c e2)
                          (Or e1 e2) -> Or (substituteOne a b c e1) (substituteOne a b c e2)
                          (Impl e1 e2) -> Impl (substituteOne a b c e1) (substituteOne a b c e2)
  where 
  substName :: Expr -> Expr -> Expr -> String -> Expr
  substName a b c "A" = a
  substName a b c "B" = b
  substName a b c "C" = c
  substName a b c _   = undefined


substitute :: Expr -> Expr -> Expr -> [Expr] -> [Expr]
substitute a b c (hd : tl) = (substituteOne a b c hd) : (substitute a b c tl)
substitute _ _ _ [] = []



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


