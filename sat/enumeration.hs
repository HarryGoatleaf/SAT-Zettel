import Text.Show.Unicode
import qualified Data.Set as Ds

subst :: Assignment
subst 'x' = Just True
subst 'y' = Just True

phi' = (substitute 'y' True (And [Or [ Var 'x', Var 'y'], Or [ Var 'x', NegVar 'y']]))
main = do
  uprint (show phi');
  uprint (evaluate (\x -> Nothing) phi')

data Literal = Var Char | NegVar Char | Val Bool
data Clause = Or [Literal]
data CNF = And [Clause]
type Assignment = (Char -> Maybe Bool)

--enumerate :: CNF -> Assignment
--enumerate phi = 
--  let hEnumuerate = \phi curAssignment
--    | (size (get_free phi)==0) && (evaluate curAssignment phi) -> 
--  in 

-- boilerplate

class Formula phi where
  get_free :: phi -> Ds.Set Char
  evaluate :: Assignment -> phi -> Maybe Bool
  substitute :: Char -> Bool -> phi -> phi

instance Formula Literal where
  get_free (Val _) = Ds.empty
  get_free (Var x) = Ds.singleton x
  get_free (NegVar x) = Ds.singleton x
  --
  evaluate _ (Val v)  = Just v
  evaluate assignment (Var x) = case assignment x of
    Just val -> Just val
    Nothing -> Nothing
  evaluate assignment (NegVar x) = case assignment x of
    Just val -> Just (not val)
    Nothing -> Nothing
  --
  substitute var val (Var x) 
    | var==x = Val val
    | otherwise = Var x
  substitute var val (NegVar x) 
    | var==x = Val (not val)
    | otherwise = NegVar x
  substitute _ _ literal = literal

instance Formula Clause where
  get_free (Or literals) = foldr Ds.union (Ds.empty) [get_free x | x <- literals]
  evaluate assignment (Or literals) 
    | any (\x -> (x==(Just True))) (map (evaluate assignment) literals) = Just True
    | all (\x -> (x==(Just False))) (map (evaluate assignment) literals) = Just False
    | otherwise = Nothing
  substitute var val (Or literals) = Or (map (substitute var val) literals)

instance Formula CNF where
  get_free (And clauses) = foldr Ds.union (Ds.empty) [get_free x | x <- clauses]
  evaluate assignment (And clauses) 
    | all (\x -> x==(Just True)) (map (evaluate assignment) clauses) = Just True
    | any (\x -> x==(Just False)) (map (evaluate assignment) clauses) = Just False
    | otherwise = Nothing
  substitute var val (And clauses) = And (map (substitute var val) clauses)

instance Show Literal where
  show (Var x) = [x]
  show (NegVar x) = "¬" ++ [x]
  show (Val val) = show val

instance Show Clause where 
  show (Or literals) = "(" ++ showHelper literals ++ ")" where
      showHelper [] = ""
      showHelper [literal] = show literal
      showHelper (literal:xs) = show  literal ++ " ∨ " ++ showHelper xs

instance Show CNF where 
  show (And clauses) = "(" ++ showHelper clauses ++ ")" where
      showHelper [] = ""
      showHelper [clauses] = show clauses
      showHelper (clause:xs) = show clause ++ " ∧ " ++ showHelper xs

a :: Int -> Int
a 5 = 1

b :: Int -> Int
b 1 = 2

c = a.b
