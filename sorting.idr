import Data.So
import Data.Vect
import Data.String
import Data.List.Views
-- Function that returns a proof that either x <= y or y <= x. Can define either for int or for nat (nat easier)
--insertion sort guy uses IsLte, MkisLte, chooseLte
--Ben uses natLTETrans, natLTEEith, totNat
-- https://stackoverflow.com/questions/61170830/idris-pass-proof-to-a-function-that-arguments-are-lte
-- ^ might be helpful if there are errors
-- Not really sure how much of this we need & we need to rework it anyway
IsLte : Ord e => (x:e) -> (y:e) -> Type
IsLte x y = So (x <= y)
mkIsLte : Ord e => (x:e) -> (y:e) -> Maybe (IsLte x y)
mkIsLte x y =
  case choose (x <= y) of 
    Left proofXLteY =>
      Just proofXLteY
    Right proofNotXLteY =>
      Nothing
  
-- Transitivity
transPfHelper : (w : LTE left right) -> (x : LTE right k) -> LTE left k
transPfHelper LTEZero LTEZero = LTEZero
transPfHelper LTEZero (LTESucc x) = LTEZero
transPfHelper (LTESucc y) (LTESucc x) = LTESucc (transPfHelper y x)

transPf :(x,y,z : Nat) ->  LTE x y -> LTE y z -> LTE x z
transPf Z Z z LTEZero LTEZero = LTEZero
transPf Z (S left) (S right) LTEZero (LTESucc x) = LTEZero
transPf (S left) (S right) (S k) (LTESucc w) (LTESucc x) =
  LTESucc (transPfHelper w x)

-- Reflexivity/anti-symmetry
reflPf : (x,y : Nat) -> Either (LTE x y) (LTE y x)
reflPf Z y = Left LTEZero
reflPf x Z = Right LTEZero
reflPf (S k) (S j) with (reflPf k j)
  reflPf (S k) (S j) | (Left l) = Left (LTESucc l)
  reflPf (S k) (S j) | (Right r) = Right (LTESucc r)



-- Prove that a given list A starts with a given list B 
-- (ie, that the head of list A is list B)
data IsHead : Vect m e1 -> Vect n e2 -> Type where
  HeadList : IsHead (x::rest1) (x::rest2)

--what the blogpost does?
-- data HeadIs : Vect n e -> e -> Type where
--    MkHeadIs : HeadIs (x::xs) x

-- Sorted Data Type
-- Nil and a Singleton List are trivially sorted
-- a list [a,b,...rest] is sorted iff a <= b and [b,...rest] is sorted
data Sorted: (lst: Vect n Nat) -> Type where
  NilSorted: Sorted(Nil)
  SingletonSorted: (element: Nat) -> Sorted(element::Nil)
  SortedCons: Sorted xs -> All (\x => y `LTE` xs -> Sorted (y::xs)

-- One version of proveSorted that we need to rework & figure out if we can work with it this way
-- /if it's better this way
proveSorted : (lst: Vect n Nat) -> Maybe(Sorted lst)
proveSorted Nil = Just NilSorted
proveSorted (element::Nil) = Just(SingletonSorted element)
proveSorted (first::(second::rest)) = 
  case (mkIsLte first second) of
    Just(proofFirstLteSecond) =>
      case (proveSorted (second::rest)) of 
        Just(proofTailSorted) =>
          Just (ListSorted first second rest proofFirstLteSecond proofTailSorted)
        Nothing =>
          Nothing
    Nothing => 
      Nothing
--

-- we need to rename this and understand it/maybe reconfigure it if we can work it?
-- takes in 3 permutations and produces a 4th one? 
-- Where the 3rd one has to have first argument be concat of first argument of first 2
-- return ListPerm of second argument concat 
-- i don't even get the function body of this really tbh
mergeSortLemma: ListPermutation x1 x2 -> ListPermutation y1 y2 ->
ListPermutation (x1 ++ y1) z -> ListPermutation (x2 ++ y2) z
mergeSortLemma perm1 perm2 perm3 = 
TransitivePermutation (listPermutationFrontAppend perm2) 
(Transitive Permutation ( listPermutationBackAppend perm1) perm3)


-- this mainly comes from the book Chapter 10 merge sort implementations, adding in the proof tuples

mergeSort: (xs: Vect n Nat) -> (ys: Vect n Nat ** (SoListrted ys, Permutation ys xs))
mergeSort input with (splitRec input)
	mergeSort [] | SplitRecNil = ([], NilSorted, NilPermutesNil)
  mergeSort [x] | SplitRecOne = ([x], SingletonSorted, SameHeadPermutes)
  mergeSort (left ++ right) | (SplitRecPair lrec rrec) = 
  let (left_side ** (left_ord, left_perm)) = mergeSort left | lrec in
  let (right_side ** (right_ord, right_perm)) = mergeSort right | rrec in
  let (total_merge ** (total_ord, total_perm))	merge left_side left_ord right_side right_ord in
  (total_merge ** (total_ord, mergeSortLemma left_perm right_perm total_perm)) -- we have everything up to this line, basically just need to combine the permutations


-- this is mainly from book chapter 3 insSort implementation
-- STILL NEEDS TO BE PROOF-IED
insert : (x : Nat) -> (xsSorted : Vect k Nat) -> (ysSorted : Vect (S k) Nat)
insert x [] = [x]
insert x (y :: xs) = case x < y of
												False => y :: insert x xs
												True => x :: y :: xs
insSort : (xs : Vect n Nat) -> (ys : Vect n Nat ** (ListPermutation xs ys, Sorted ys))
insSort [] = ([] ** (NilPermutesNil, NilSorted))
insSort (x :: xs) = let xsSorted = insSort xs in
												insert x xsSorted


-- I think in terms of IO, the best thing is done by Insertion Sort guy:
--But we can make some modifications using built in functions parseInteger and intersperse

convToString: Integer -> String
convToString s = the String (cast s)

main : IO ()
main = do
    putStrLn "Please type a space-separated list of integers: "
    csv <- getLine
    let numbers = map (fromMaybe 0 . parseInteger) (words csv) 
    --now you just need to sort them with a funct that goes from List Nat -> List Nat 
	-- let sorted_numbers = ____sort numbers
    putStrLn "After sorting, the integers are: "
    -- print sorted_numbers
    putStrLn ""
    --or if you want to make them space separated as well
   	-- putStrLn $ concat $ intersperse " " (map convToString sorted_numbers)
  
  