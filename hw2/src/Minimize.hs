module Minimize where

import LogicParser
import Data.Map
import Data.Set

-- This class can store information about processed proof
-- Store global reverse forMP hypotheses meta
-- where global is general mapping from expression to index (use to store)
-- reverse is mapping from index to expression (use to retrieve info for mp)
-- forMP is mapping for modus ponens
-- hypotheses is a list of known hypotheses
-- meta is information about strings of proof
data Storage = Store (Map Expr Int) 
                     (Map Int Expr)
                     (Map Expr [Int])
                     (Map Expr Int)
                     [MetaInfo] deriving (Show)

data MetaInfo = Incorrect          |
                Duplicate          |
                Hypothesis Int     |
                Axiom Int          |
                ModusPonens Int Int deriving (Eq, Show)

putIntoComputer :: Expr -> Int -> Storage -> Storage
putIntoComputer expr index (Store gl rev mp hyp states) =
        Store new_gl new_rev new_mp hyp new_states
        where new_meta = helper expr gl rev mp hyp 
              new_states = new_meta : states
              new_rev = Data.Map.insert index expr rev
              new_gl = if non_trivial new_meta then Data.Map.insert expr index gl else gl
              new_mp = if non_trivial new_meta then tryPut expr index mp else mp


non_trivial :: MetaInfo -> Bool
non_trivial (Incorrect) = False
non_trivial (Duplicate) = False
non_trivial _ = True

tryPut :: Expr -> Int -> Map Expr [Int] -> Map Expr [Int]
tryPut (Impl l r) ind mp = update (\list -> Just (ind : list)) r (updated r mp)
tryPut _ _ mp = mp

updated :: Ord k => k -> Map k [a] -> Map k [a]
updated key mp = if not (isJust (key `Data.Map.lookup` mp)) then Data.Map.insert key [] mp else mp

helper :: Expr -> Map Expr Int -> Map Int Expr -> Map Expr [Int] -> Map Expr Int -> MetaInfo
helper expr gl rev mp hyp = if (isJust $ Data.Map.lookup expr gl) then
                               Duplicate 
                               else if (isAxiom expr) then
                                    getAxiom expr
                                    else if (isHypothesis expr hyp) then
                                         getHypothesis expr hyp 
                                         else if (isModusPonens expr gl rev mp) then
                                              getModusPonens expr gl rev mp
                                              else Incorrect

isAxiom :: Expr -> Bool
isAxiom e = matcher $ getAxiom e
            where matcher (Axiom 0) = False
                  matcher (Axiom _) = True
                  matcher _ = False

getAxiom :: Expr -> MetaInfo
getAxiom e = Axiom $ getAxiomHelper 1 mainAxioms e 

getAxiomHelper :: Int -> [Expr] -> Expr -> Int
getAxiomHelper _ [] _ = 0
getAxiomHelper i (hd : tl) e = if checkSubstitution hd e then i 
                               else getAxiomHelper (i + 1) tl e

isHypothesis :: Expr -> Map Expr Int -> Bool
isHypothesis e mp = isJust $ (e `Data.Map.lookup` mp)

getHypothesis :: Expr -> Map Expr Int -> MetaInfo
getHypothesis e mp= Hypothesis $ mp ! e

isModusPonens :: Expr -> Map Expr Int -> Map Int Expr -> Map Expr [Int] -> Bool
isModusPonens e gl rev mp = case getModusPonens e gl rev mp of 
                            ModusPonens 0 0 -> False
                            _ -> True

getModusPonens :: Expr -> Map Expr Int -> Map Int Expr -> Map Expr [Int] -> MetaInfo
getModusPonens e gl rev mp = case unwrapMP gl rev (e `Data.Map.lookup` mp) of (a, b) -> ModusPonens a b

unwrapMP :: Map Expr Int -> Map Int Expr -> Maybe [Int] -> (Int, Int)
unwrapMP gl rev (Just (ind : tl)) = if isJust $ leftPart 
                                    then (fromJust leftPart, ind)
                                    else unwrapMP gl rev (Just tl) 
                                    where 
                                    fullExpr = rev ! ind
                                    leftExpr = case fullExpr of
                                               (Impl l _) -> l
                                    leftPart = leftExpr `Data.Map.lookup` gl
unwrapMP _ _ _ = (0, 0)


--axioms

firstAxiom :: Expr 
firstAxiom = Impl (Var "a") (Impl (Var "b") (Var "a"))

vA :: Expr
vA = Var "a"

vB :: Expr
vB = Var "b"

vC :: Expr
vC = Var "c"

mainAxioms :: [Expr]
mainAxioms = [
    Impl vA (Impl vB vA),
    Impl (Impl vA vB) (Impl (Impl vA (Impl vB vC)) (Impl vA vC)),
    Impl vA (Impl vB (And vA vB)),
    Impl (And vA vB) vA,
    Impl (And vA vB) vB,
    Impl vA (Or vA vB),
    Impl vB (Or vA vB),
    Impl (Impl vA vC) (Impl (Impl vB vC) (Impl (Or vA vB) vC)),
    Impl (Impl vA vB) (Impl (Impl vA (Neg vB)) (Neg vA)),
    Impl (Neg (Neg vA)) vA]


checkSubstitution :: Expr -> Expr -> Bool
checkSubstitution axiom target = checkMap 
    where
    mp :: Map String (Maybe Expr)
    mp = axiomHelper axiom target
    checkMap = Data.Map.foldr (\x val -> val && isJust x) True mp

merger :: Expr -> Expr -> Expr -> Expr -> Map String (Maybe Expr)
merger la ra le re = unionWith 
                     (\x y -> if (x == y) then x else Nothing) 
                     (axiomHelper la le)
                     (axiomHelper ra re) 



axiomHelper :: Expr -> Expr -> Map String (Maybe Expr)
axiomHelper (Impl la ra) (Impl le re) = merger la ra le re
axiomHelper (Or la ra) (Or le re) = merger la ra le re
axiomHelper (And la ra) (And le re) = merger la ra le re
axiomHelper (Neg x) (Neg y) = merger x x y y
axiomHelper (Var x) e = Data.Map.insert x (Just e) Data.Map.empty 
axiomHelper _ _ = Data.Map.insert "z" Nothing Data.Map.empty



unwrapProof :: Storage -> [(Expr, MetaInfo)]
unwrapProof (Store _ rev _ _ meta) = normalize $ unwrapStorageHelper metalen meta rev (Data.Set.singleton metalen)
    where metalen = length meta

-- Another int in tuple is for true number
unwrapStorageHelper :: Int -> [MetaInfo] -> Map Int Expr -> Set Int 
                       -> [(Expr, MetaInfo, Int)]
unwrapStorageHelper ind (hd : tl) rev known =
         if Data.Set.member ind known then
         case hd of
            ModusPonens x y -> (rev ! ind, hd, ind) : (unwrapStorageHelper (ind - 1) tl rev (Data.Set.insert x (Data.Set.insert y known)))
            Hypothesis x -> (rev ! ind, hd, ind) : (unwrapStorageHelper (ind - 1) tl rev known)
            Axiom x -> (rev ! ind, hd, ind) : (unwrapStorageHelper (ind - 1) tl rev known)
            _ -> unwrapStorageHelper (ind - 1) tl rev known
         else
         unwrapStorageHelper (ind - 1) tl rev known
unwrapStorageHelper _ [] _ _ = []



reverseList :: [a] -> [a]
reverseList [] = []
reverseList (x:xs) = reverseList xs ++ [x]

normalize :: [(Expr, MetaInfo, Int)] -> [(Expr, MetaInfo)]
normalize list = normalizeHelper (reverseList list) Data.Map.empty 1

normalizeHelper :: [(Expr, MetaInfo, Int)] -> Map Int Int -> Int -> [(Expr, MetaInfo)] 
normalizeHelper ((e, meta, ind) : tl) mp trueind = (e, modifiedMeta) : normalizeHelper tl modmp (trueind + 1)
                where
                modify meta mp = case meta of
                                 (ModusPonens x y) -> ModusPonens (mp ! x) (mp ! y)
                                 _ -> meta
                modifiedMeta = modify meta mp
                modmp = Data.Map.insert ind trueind mp 
normalizeHelper [] _ _ = []

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust _ = False

fromJust :: Maybe a -> a
fromJust (Just x) = x
fromJust _ = undefined


format_meta :: MetaInfo -> Int -> String
format_meta (Hypothesis num) ind = "[" ++ show ind ++ ". Hypothesis " ++ show num ++ "]"
format_meta (Axiom x) ind        = "[" ++ show ind ++ ". Ax. sch. " ++ show x ++ "]"
format_meta (ModusPonens x y) ind = "[" ++ show ind ++ ". M.P. " ++ show y ++ ", " ++ show x ++ "]"
format_meta _ _ = "Error"

strip :: Storage -> Expr -> Storage
strip (Store a b c d l) e = stripHelper (Store a b c d l) e (length l)

stripHelper :: Storage -> Expr -> Int -> Storage
stripHelper (Store a rev c d (x:tl)) e ind = case x of
                                       Duplicate -> stripHelper (Store a rev c d tl) e (ind - 1)
                                       _ -> if isJust (e `Data.Map.lookup` a) && (a ! e == ind) 
                                            then Store a rev c d (x:tl)
                                            else stripHelper (Store a rev c d tl) e (ind - 1)
stripHelper s e ind = s 


check_correctness :: Storage -> Bool 
check_correctness (Store a b c d l) = checkValid l 
                where 
                checkValid (Incorrect:tail) = False
                checkValid (_:tail) = checkValid tail
                checkValid [] = True
