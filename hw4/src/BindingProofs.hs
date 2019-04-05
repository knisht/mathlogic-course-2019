module BindingProofs where

import DeductionTheorem
import Grammar
import ParseModule


mapToExprTuple :: (String, a) -> (Expr, a)
mapToExprTuple (x, y) = (getExpr x, y)

substituteHelper :: Expr -> Expr -> Expr -> (Expr, DeductionMetaInfo) -> (Expr, DeductionMetaInfo)
substituteHelper a b c = (\(x, y) -> (substituteOne a b c x, case y of
                                                               AxiomD -> AxiomD
                                                               ModusPonensD e -> ModusPonensD $ substituteOne a b c e))


pTTAnd x y = substituteHelper x y undefined <$>
  mapToExprTuple <$> [
  ("A -> B -> A&B", AxiomD),
  ("B -> A&B", ModusPonensD (getExpr "A")),
  ("A&B", ModusPonensD (getExpr "B"))
  ]             

pTFAnd x y = substituteHelper x y undefined <$>
  mapToExprTuple <$> [
  ("((A&B) -> B) -> ((A&B) -> !B) -> !(A&B)", AxiomD),
  ("A&B -> B", AxiomD),
  ("!B -> (A&B) -> !B", AxiomD),
  ("(A&B) -> !B", ModusPonensD (getExpr "!B")),
  ("(A&B -> !B) -> !(A&B)", ModusPonensD (getExpr "(A&B -> B)")),
  ("!(A&B)", ModusPonensD (getExpr "A&B -> !B"))
  ]

pFTAnd x y = substituteHelper x y undefined <$>
  mapToExprTuple <$> [
  ("((A&B) -> A) -> ((A&B) -> !A) -> !(A&B)", AxiomD),
  ("A&B -> A", AxiomD),
  ("!A -> (A&B) -> !A", AxiomD), 
  ("(A&B) -> !A", (ModusPonensD (getExpr "!A"))),
  ("(A&B -> !A) -> !(A&B)", ModusPonensD (getExpr "A&B -> A")),
  ("!(A&B)", ModusPonensD (getExpr "A&B -> !A"))
  ]
 
pTTOr x y = substituteHelper x y undefined <$> 
  mapToExprTuple <$> [
  ("A -> A|B", AxiomD),
  ("A|B", ModusPonensD (getExpr "A"))
  ]

pFTOr x y = substituteHelper x y undefined <$>
  mapToExprTuple <$> [
  ("B -> A | B", AxiomD),
  ("A|B", ModusPonensD (getExpr "B"))
  ]

pFFOr x y = substituteHelper x y undefined <$>
  (mapToExprTuple <$> [
  ("(A|B -> A) -> (A|B -> !A) -> !(A|B)", AxiomD),
  ("(A -> A) -> (B -> A) -> (A|B -> A)", AxiomD),
  ("A -> (A -> A) -> A", AxiomD),
  ("A -> A -> A", AxiomD),
  ("(A -> A -> A) -> (A -> (A -> A) -> A) -> (A -> A)", AxiomD),
  ("(A -> (A -> A) -> A) -> (A -> A)", ModusPonensD (getExpr "A -> A -> A")),
  ("A -> A", ModusPonensD (getExpr "A -> (A -> A) -> A"))
  ])
  ++
  (unwrapDeduction (getExpr "!B") (unwrapDeduction (getExpr "B") contradiction))
  ++ 
  (mapToExprTuple <$> [
  ("B -> A", ModusPonensD (getExpr "!B")),
  ("(B -> A) -> (A|B -> A)", ModusPonensD (getExpr "A -> A")),
  ("(A|B) -> A", ModusPonensD (getExpr "B -> A")),
  ("(A|B -> !A) -> !(A|B)", ModusPonensD (getExpr "A|B -> A")),
  ("!A -> A|B -> !A", AxiomD),
  ("A|B -> !A", ModusPonensD (getExpr "!A")),
  ("!(A | B)", ModusPonensD (getExpr "A|B -> !A"))
  ])

contradiction :: [(Expr, DeductionMetaInfo)]
contradiction = 
  mapToExprTuple <$> [
  ("B -> !A -> B", AxiomD),
  ("!B -> !A -> !B", AxiomD),
  ("!B", AxiomD),
  ("B", AxiomD),
  ("!A -> B", ModusPonensD (getExpr "B")),
  ("!A -> !B", ModusPonensD (getExpr "!B")),
  ("(!A -> B) -> (!A -> !B) -> !!A", AxiomD),
  ("(!A -> !B) -> !!A", ModusPonensD (getExpr "!A -> B")),
  ("!!A", ModusPonensD (getExpr "!A -> !B")),
  ("!!A -> A", AxiomD),
  ("A", ModusPonensD (getExpr "!!A"))
  ]

pNegNeg x = substituteHelper x undefined undefined <$>
  mapToExprTuple <$> [
  ("(!A -> A) -> (!A -> !A) -> !!A", AxiomD),
  ("A -> !A -> A", AxiomD),
  ("!A -> A", ModusPonensD (getExpr "A")),
  ("(!A -> !A) -> !!A", ModusPonensD (getExpr "!A -> A")),
  ("!A -> !A -> !A", AxiomD),
  ("!A -> (!A -> !A) -> !A", AxiomD),
  ("(!A -> !A -> !A) -> (!A -> (!A -> !A) -> !A) -> (!A -> !A)", AxiomD),
  ("(!A -> (!A -> !A) -> !A) -> (!A -> !A)", ModusPonensD (getExpr "!A -> !A -> !A")),
  ("!A -> !A", ModusPonensD (getExpr "!A -> (!A -> !A) -> !A")),
  ("!!A", ModusPonensD (getExpr "!A -> !A"))
  ]


pTTImpl x y = substituteHelper x y undefined <$>
  mapToExprTuple <$> [
  ("B -> A -> B", AxiomD),
  ("A -> B", ModusPonensD (getExpr "B"))
  ]

pFTImpl x y = substituteHelper x y undefined <$>
  (mapToExprTuple <$> [
  ("(A -> !A) -> (A -> !A -> B) -> (A -> B)", AxiomD),
  ("!A -> A -> !A", AxiomD),
  ("A -> !A", ModusPonensD (getExpr "!A")),
  ("(A -> !A -> B) -> (A -> B)", ModusPonensD (getExpr "A -> !A"))
  ])
  ++ 
  (unwrapDeduction (getExpr "A") (unwrapDeduction (getExpr "!A") contradiction2))
  ++
  (mapToExprTuple <$> [
  ("(A -> B)", ModusPonensD (getExpr "A -> !A -> B"))
  ])

contradiction2 :: [(Expr, DeductionMetaInfo)]
contradiction2 = 
  mapToExprTuple <$> [
  ("A -> !B -> A", AxiomD),
  ("!A -> !B -> !A", AxiomD),
  ("!A", AxiomD),
  ("A", AxiomD),
  ("!B -> A", ModusPonensD (getExpr "A")),
  ("!B -> !A", ModusPonensD (getExpr "!A")),
  ("(!B -> A) -> (!B -> !A) -> !!B", AxiomD),
  ("(!B -> !A) -> !!B", ModusPonensD (getExpr "!B -> A")),
  ("!!B", ModusPonensD (getExpr "!B -> !A")),
  ("!!B -> B", AxiomD),
  ("B", ModusPonensD (getExpr "!!B"))
  ]



pTFImpl x y = substituteHelper x y undefined <$>
  mapToExprTuple <$> [
  ("((A -> B) -> B) -> ((A -> B) -> !B) -> !(A -> B)", AxiomD),
  ("((A -> B) -> A) -> ((A -> B) -> (A -> B)) -> ((A -> B) -> B)", AxiomD),
  ("(A -> B) -> (A -> B) -> (A -> B)", AxiomD),
  ("(A -> B) -> ((A -> B) -> (A -> B)) -> (A -> B)", AxiomD),
  ("((A -> B) -> (A -> B) -> (A -> B)) -> ((A -> B) -> ((A -> B) -> (A -> B)) -> (A -> B)) -> ((A -> B) -> (A -> B))", AxiomD),
  ("((A -> B) -> ((A -> B) -> (A -> B)) -> (A -> B)) -> ((A -> B) -> (A -> B))", ModusPonensD (getExpr "(A -> B) -> (A -> B) -> (A -> B)")),
  ("((A -> B) -> (A -> B))", ModusPonensD (getExpr "(A -> B) -> ((A -> B) -> (A -> B)) -> (A -> B)")),
  ("!B -> (A -> B) -> !B", AxiomD),
  ("(A -> B) -> !B", ModusPonensD (getExpr "!B")),
  ("A -> (A -> B) -> A", AxiomD),
  ("(A -> B) -> A", ModusPonensD (getExpr "A")),
  ("((A -> B) -> (A -> B)) -> ((A -> B) -> B)", ModusPonensD (getExpr "(A -> B) -> A")),
  ("((A -> B) -> B)", ModusPonensD (getExpr "(A -> B) -> (A -> B)")),
  ("((A -> B) -> !B) -> !(A -> B)", ModusPonensD (getExpr "(A -> B) -> B")),
  ("!(A -> B)", ModusPonensD (getExpr "(A -> B) -> !B"))
  ]



contraposition a b = substituteHelper a b undefined <$> contrapose_raw


contrapose_raw = 
  (mapToExprTuple <$>
  [
  ("(A -> B) -> (A -> !B) -> !A", AxiomD), 
  ("((A -> B) -> (A -> !B) -> !A) -> !B -> ((A -> B) -> (A -> !B) -> !A)", AxiomD),
  ("!B -> ((A -> B) -> (A -> !B) -> !A)", ModusPonensD (getExpr "(A -> B) -> (A -> !B) -> !A")),
  ("(A -> B) -> !B -> (A -> B)", AxiomD),
  ("A -> B", AxiomD),
  ("!B -> (A -> B)", ModusPonensD (getExpr "A -> B")),
  ("!B -> (A -> !B)", AxiomD),
  ("(!B -> (A -> B)) -> (!B -> ((A -> B) -> (A -> !B) -> !A)) -> (!B -> (A -> !B) -> !A)", AxiomD),
  ("((!B -> ((A -> B) -> (A -> !B) -> !A)) -> (!B -> (A -> !B) -> !A))", ModusPonensD (getExpr "!B -> (A -> B)")),
  ("!B -> (A -> !B) -> !A", ModusPonensD (getExpr "(!B -> ((A -> B) -> (A -> !B) -> !A))")),
  ("(!B -> A -> !B) -> (!B -> (A -> !B) -> !A) -> (!B -> !A)", AxiomD),
  ("(!B -> (A -> !B) -> !A) -> (!B -> !A)", ModusPonensD (getExpr "!B -> (A -> !B)")),
  ("!B -> !A", ModusPonensD (getExpr "!B -> (A -> !B) -> !A"))
  ]) 


disjunctedThird e = substituteHelper e undefined undefined <$>
  (mapToExprTuple <$> [("A -> A | !A", AxiomD)])
  ++ (contraposition (getExpr "A") (getExpr "A | !A"))
  ++ (mapToExprTuple <$> [("!A -> A | !A", AxiomD)])
  ++ (contraposition (getExpr "!A") (getExpr "A | !A"))
  ++ (mapToExprTuple <$> [
  ("(!(A|!A) -> !A) -> (!(A|!A) -> !!A) -> !!(A|!A)", AxiomD),
  ("(!(A|!A) -> !!A) -> !!(A|!A)", ModusPonensD (getExpr "!(A|!A) -> !A")),
  ("!!(A|!A)", ModusPonensD (getExpr "!(A|!A) -> !!A")),
  ("!!(A|!A) -> (A|!A)", AxiomD),
  ("A|!A", ModusPonensD (getExpr "!!(A|!A)"))
  ])
