
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
  
  