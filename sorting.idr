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

-- datatype to show that two lists are permutations
data ListPermutation : (xlst: Vect n e) -> (ylst: Vect n e) -> Type where
	NilPermutesNil: ListPermutation Nil Nil
	SameHeadPermutes:
		(x:e) -> ListPermutation a b -> ListPermutation (x::a) (x::b)
	SameFirstTwoPermutes:
		(x:e) -> (y:e) -> ListPermutation a b -> ListPermutation(x::(y::a)) (y::(x::b))
	TransitivePermutation:
		ListPermutation a b -> ListPermutation b c -> ListPermutation a c

listPermutationReflexive: ListPermutation xs xs
listPermutationReflexive {xs = []} = PermNil
listPermutationReflexive {xs = x :: xs} = SameHeadPermutes (listPermutationReflexive {xs=xs})

listPermutationSymmetric: ListPermutation xs ys -> ListPermutation ys xs
listPermutationSymmetric NilPermutesNil = NilPermutesNil
listPermutationSymmetric (SameHeadPermutes x) = SameHeadPermutes(listPermutationSymmetric  x)
listPermutationSymmetric SameFirstTwoPermutes = SameFirstTwoPermutes
listPermutationSymmetric (TransitivePermutation x y) = TransitivePermutation (listPermutationSymmetric y) (listPermutationSymmetric x)

listPermutationFrontAppend: ListPermutation xs xs' -> ListPermutation (ys ++ xs) (ys ++ xs')
listPermutationFrontAppend {ys=[]} p = p
listPermutationFrontAppend {ys={y::ys}} p = SameHeadPermutes (listPermutationFrontAppend p)

listPermutationBackAppend: ListPermutation xs xs' -> ListPermutation (xs ++ ys) (xs' ++ ys)
listPermutationBackAppend NilPermutesNil = permRefl
listPermutationBackAppend (SameHeadPermutes p) = SameHeadPermutes (listPermutationBackAppend p)
listPermutationBackAppend SameFirstTwoPermutes = SameFirstTwoPermutes
listPermutationBackAppend (TransitivePermutation x y) = TransitivePermutation (listPermutationBackAppend x) (listPermutationBackAppend y)

listPermutationCommutative: ListPermutation (xs ++ ys) (ys ++ xs)
listPermutationCommutative {xs=[]} {ys=ys} = 
    rewrite appendNilRightNeutral ys in 
    listPermutationReflexive
listPermutationCommutative {xs=(x::xs)} {ys=[]} = 
    rewrite appendNilRightNeutral (x :: xs) in 
    listPermutationReflexive
listPermutationCommutative {xs=(x::xs)} {ys=(y::ys)} = 
	TransitivePermutation 
  	(SameHeadPermutes 
    	(TransitivePermutation 
      	(listPermutationCommutative {xs=xs} {ys=y::ys})
        (SameHeadPermutes (listPermutationSymmetric (listPermutationCommutative {xs=xs} {ys=ys}))
    (TransitivePermutation SameFirstTwoPermutes (SameHeadPermutes (listPermutationCommutative {xs=x::xs} {ys=ys} )))


data All: (a -> Type) -> Vect n a -> Type where
	AllNil: All p []
  AllCons: p x -> All p xs -> All p (x::xs)
  
allLTETransitiveProperty: LTE x y -> All (LTE y) ys -> All (LTE x) ys
allLTETransitiveProperty _ AllNil = AllNil
allLTETransitiveProperty xltey (AllCons p allys) = AllCons (lteTransitive xxltey p) (allLTEtrans xltey allys)

allAppendTwoLists: All p xs -> All p ys -> All p (xs + ys)
allAppendTwoLists AllNil p = p
allAppendTwoLists (AllCons px x) ally = AllCons px (allAppend allx ally)



mergeLists: (xs: List Nat) -> Sorted xs -> (ys: List Nat) -> Sorted ys ->
	(zs: List Nat ** (Ordered zs, Permutation (xs ++ ys) zs))
mergeLists [] _ ys orderedys = (ys ** (orderedys, reflexivePermutation))
mergeLists xs orderedxs [] _ =
	rewrite appendNilRightNeutral xs in (xs ** (orderedxs, reflexivePermutation))
mergeLists (x::xs) (ListSorted (x::xs)) (y::ys) (ListSorted (y::ys)) with (isLTE x y)
	| Yes ltexy =
  	let (zs ** (orderedxz, permsz)) = (merge xs 

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
  
  