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
data IsHead : List e1 -> List e2 -> Type where
  HeadList : IsHead (x::rest1) (x::rest2)

--what the blogpost does?
-- data HeadIs : Vect n e -> e -> Type where
--    MkHeadIs : HeadIs (x::xs) x

-- One version of proveSorted that we need to rework & figure out if we can work with it this way
-- /if it's better this way
-- proveSorted : (lst: Vect n Nat) -> Maybe(Sorted lst)
-- proveSorted Nil = Just NilSorted
-- proveSorted (element::Nil) = Just(SingletonSorted element)
-- proveSorted (first::(second::rest)) = 
--   case (mkIsLte first second) of
--     Just(proofFirstLteSecond) =>
--       case (proveSorted (second::rest)) of 
--         Just(proofTailSorted) =>
--           Just (ListSorted first second rest proofFirstLteSecond proofTailSorted)
--         Nothing =>
--           Nothing
--     Nothing => 
--       Nothing
--

-- datatype to show that two lists are permutations
data ListPermutation : List a -> List a -> Type where
    NilPermutesNil: ListPermutation Nil Nil
    SameHeadPermutes:
      ListPermutation a b -> ListPermutation (x::a) (x::b)
    SameFirstTwoPermutes: ListPermutation(x::y::a) (y::x::a)
    MiddleElementPermutes:
      ListPermutation (a++b) (c::d) -> ListPermutation (a++x::b) (c::x::d)
    TransitivePermutation:
      ListPermutation a b -> ListPermutation b c -> ListPermutation a c
    ConcatentationPermutes : ListPermutation a b -> ListPermutation c d -> ListPermutation (a ++ c) (b ++ d)



listPermutationReflexive: ListPermutation xs xs
listPermutationReflexive {xs = []} = NilPermutesNil
listPermutationReflexive {xs = x :: xs} = SameHeadPermutes (listPermutationReflexive {xs=xs})

listPermutationSymmetric: ListPermutation xs ys -> ListPermutation ys xs
listPermutationSymmetric NilPermutesNil = NilPermutesNil
listPermutationSymmetric (SameHeadPermutes x) = SameHeadPermutes (listPermutationSymmetric  x)
listPermutationSymmetric SameFirstTwoPermutes = SameFirstTwoPermutes
listPermutationSymmetric (TransitivePermutation x y) = TransitivePermutation (listPermutationSymmetric y) (listPermutationSymmetric x)

listPermutationFrontAppend: ListPermutation xs xs' -> ListPermutation (ys ++ xs) (ys ++ xs')
listPermutationFrontAppend {ys=[]} p = p
listPermutationFrontAppend {ys=(y::ys)} p = SameHeadPermutes (listPermutationFrontAppend p)

listPermutationBackAppend: ListPermutation xs xs' -> ListPermutation (xs ++ ys) (xs' ++ ys)
listPermutationBackAppend NilPermutesNil = listPermutationReflexive
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
        (SameHeadPermutes (listPermutationSymmetric (listPermutationCommutative {xs=xs} {ys=ys})))
      )
    )
    (TransitivePermutation SameFirstTwoPermutes (SameHeadPermutes (listPermutationCommutative {xs=x::xs} {ys=ys} )))


data All: (a -> Type) -> List a -> Type where 
  AllNil: All p []
  AllCons: p x -> All p xs -> All p (x::xs)
  
allLTETransitiveProperty: LTE x y -> All (LTE y) ys -> All (LTE x) ys
allLTETransitiveProperty _ AllNil = AllNil
allLTETransitiveProperty xltey (AllCons p allys) = AllCons (lteTransitive xltey p) (allLTETransitiveProperty xltey allys)

allAppendTwoLists: All p xs -> All p ys -> All p (xs ++ ys)
allAppendTwoLists AllNil p = p
allAppendTwoLists (AllCons px allx) ally = AllCons px (allAppendTwoLists allx ally)

allSurvivesPermutation: All p xs -> ListPermutation xs ys -> All p ys
allSurvivesPermutation _ NilPermutesNil = AllNil
allSurvivesPermutation (AllCons px pxs) (SameHeadPermutes perms) = AllCons px (allSurvivesPermutation pxs perms)
allSurvivesPermutation pxs (TransitivePermutation x y) = allSurvivesPermutation (allSurvivesPermutation pxs x) y
allSurvivesPermutation (AllCons p1 (AllCons p2 all)) SameFirstTwoPermutes = AllCons p2 (AllCons p1 all)

-- Sorted Data Type
-- Nil and a Singleton List are trivially sorted
-- a list [a,b,...rest] is sorted iff a <= b and [b,...rest] is sorted
data Sorted: (lst: List Nat) -> Type where
  NilSorted: Sorted(Nil)
  SingletonSorted: (element: Nat) -> Sorted(element::Nil)
  SortedCons: Sorted xs -> All (\x => y `LTE` x) xs -> Sorted (y::xs)

mergeLowerElement: All (LTE x) xs -> All (LTE y) ys -> LTE x y -> 
  ListPermutation (xs ++ (y::ys)) zs -> All (LTE x) zs
mergeLowerElement xsltex ysltey xltey perm = 
  allSurvivesPermutation
    (allAppendTwoLists
      xsltex
      (AllCons
        xltey
        (allLTETransitiveProperty xltey ysltey)
      )
    )
    perm

mergeLists: (xs: List Nat) -> Sorted xs -> (ys: List Nat) -> Sorted ys ->
	(zs: List Nat ** (Sorted zs, ListPermutation (xs ++ ys) zs))
mergeLists [] _ ys orderedys = (ys ** (orderedys, listPermutationReflexive))
mergeLists xs orderedxs [] _ =
	rewrite appendNilRightNeutral xs in (xs ** (orderedxs, listPermutationReflexive))
mergeLists (x::xs) (SortedCons orderedxs p1) (y::ys) (SortedCons orderedys p2) with (isLTE x y)
    | Yes ltexy =
        let (zs ** (orderedzs, permzs)) = (mergeLists xs orderedxs (y::ys) (SortedCons orderedys p2)) in 
        let orderedxzs = SortedCons orderedzs (mergeLowerElement p1 p2 ltexy permzs) in
        ((x::zs) ** (orderedxzs, SameHeadPermutes permzs))
    | No lteyx =
          let Yes yltex = (isLTE y x) in
          let (zs ** (orderedzs, permzs)) = mergeLists (x::xs) (SortedCons orderedxs p1) ys orderedys in
          let ordyzs = SortedCons orderedzs (mergeLowerElement p2 p1 yltex (TransitivePermutation listPermutationCommutative permzs)) in
          let tmp = SameHeadPermutes (TransitivePermutation listPermutationCommutative permzs) in
          let permyzs = TransitivePermutation (listPermutationCommutative {xs = (x::xs)}) tmp in
          (y::zs ** (ordyzs, permyzs))

-- -- we need to rename this and understand it/maybe reconfigure it if we can work it?
-- -- takes in 3 permutations and produces a 4th one? 
-- -- Where the 3rd one has to have first argument be concat of first argument of first 2
-- -- return ListPerm of second argument concat 
-- -- i don't even get the function body of this really tbh
mergeSortLemma: ListPermutation x1 x2 -> ListPermutation y1 y2 ->
ListPermutation (x2 ++ y2) z -> ListPermutation (x1 ++ y1) z
-- mergeSortLemma perm1 perm2 perm3 = 
--   TransitivePermutation (listPermutationFrontAppend perm2) 
--   (TransitivePermutation ( listPermutationBackAppend perm1) perm3)
mergeSortLemma p1 p2 p = 
  TransitivePermutation (listPermutationFrontAppend p2) (TransitivePermutation (listPermutationBackAppend p1) p)

-- -- this mainly comes from the book Chapter 10 merge sort implementations, adding in the proof tuples

mergeSort: (xs: List Nat) -> (ys: List Nat ** (Sorted ys, ListPermutation xs ys))
mergeSort input with (splitRec input)
      mergeSort [] | SplitRecNil = ([] ** (NilSorted, listPermutationReflexive))
      mergeSort [x] | SplitRecOne = ([x] ** ((SortedCons NilSorted AllNil), listPermutationReflexive))
      mergeSort (left ++ right) | (SplitRecPair lrec rrec) = 
        let (left_side ** (left_ord, left_perm)) = (mergeSort left | lrec) in
        let (right_side ** (right_ord, right_perm)) = (mergeSort right | rrec) in
        let (total_merge ** (total_ord, total_perm)) = mergeLists left_side left_ord right_side right_ord in
        (total_merge ** (total_ord, mergeSortLemma left_perm right_perm total_perm))

-- -- this is mainly from book chapter 3 insSort implementation
insertSingleElement: (xs: List Nat) -> (Sorted xs) -> (x: Nat) -> (ys: List Nat ** (Sorted ys, ListPermutation ys (x::xs)))
insertSingleElement Nil _ x = ([x] ** ((SortedCons NilSorted AllNil), 
  listPermutationReflexive
))
insertSingleElement (x::xs) (SortedCons xsordered xltexs) y with (isLTE y x)
        | Yes lteyx = 
            ((y::x::xs) ** 
              (
                (SortedCons 
                  (SortedCons xsordered xltexs) 
                  (AllCons 
                    lteyx 
                    (allLTETransitiveProperty lteyx xltexs)
                  )
                ),
                listPermutationReflexive
              )
            )
        | No lteyx =
          let Yes xltey = (isLTE x y) in
          let (zs ** (orderedzs, permzs)) = (insertSingleElement xs xsordered y) in
            (
              (x::zs) **
              (
                (SortedCons
                  orderedzs 
                  (
                    allSurvivesPermutation
                      (AllCons xltey xltexs)
                      -- AllCons: p x -> All p xs -> All p (x::xs)
                      (listPermutationSymmetric permzs)
                  )
                ),
                (TransitivePermutation 
                  (SameHeadPermutes permzs)
                  -- ?first
                  SameFirstTwoPermutes
                )
              )
            )

-- (xs: List Nat) -> (Sorted xs) -> (x: Nat) -> (ys: List Nat ** (Sorted ys, ListPermutation ys (x::xs)))

-- insert : (xsNew : List Nat) ->
--          (x : Nat) ->
--          (Sorted xs_ord) ->
--          (ys : List Nat ** ((Sorted ys), (ListPermutation (x::xsNew) ys)))
-- insert [] x y = ([x] ** (p1, p2)) where
--   p1 = SingletonSorted x
--   p2 = SameHeadPermutes NilPermutesNil
-- insert (z :: xs) x y =
--   let headPf = IsHead [z] (z::xs) in
--       let (res ** (p1, p2, p3)) = ?insertHelper (z::xs) x y headPf in
--           (res ** (p1, p3))

-- insertSingleElement: (xs: List Nat) -> (Sorted xs) -> (x: Nat) -> (ys: List Nat ** (Sorted ys, ListPermutation ys (x::xs)))


insSort : (xs : List Nat) -> 
          (ys : List Nat ** (Sorted ys, ListPermutation xs ys))
insSort [] = ([] ** (NilSorted, NilPermutesNil))
insSort (x::xs) = 
  let (xsNew ** (xs_ord, xs_perm)) = insSort xs in
  let (total_list ** (total_ord, total_perm)) = insertSingleElement xsNew xs_ord x in
  let total_perm_rev = listPermutationSymmetric total_perm in
  let match = TransitivePermutation (SameHeadPermutes xs_perm) total_perm_rev in
  (total_list ** (total_ord, match))

-- -- I think in terms of IO, the best thing is done by Insertion Sort guy:
-- --But we can make some modifications using built in functions parseInteger and intersperse

partition: (p: Nat) -> (xs: List Nat) -> (as : List Nat ** 
  bs : List Nat **
  ( (All (\x => LTE x p) as)
  , (All (\x => LTE p x) bs)
  , ListPermutation (as ++ bs) (p::xs)
  )
)
partition p [] = ([p] ** [] ** (
  (AllCons lteRefl AllNil),
  AllNil,
  listPermutationReflexive)
  )
partition p (x::xs) with (isLTE x p)
      | Yes ltexp = 
        let (a ** b ** (allALteP, pLteAllB, perm )) = partition p xs in
        (
          x::a ** b ** (
            (
              AllCons ltexp allALteP
            ),
            pLteAllB, 
            (
                TransitivePermutation 
                (SameHeadPermutes perm)
                SameFirstTwoPermutes
            )
          )
        )
      | No lteyx =
        let Yes pltex = (isLTE p x) in
        let (a ** b ** (allALteP, pLteAllB, perm )) = partition p xs in
        (
          a ** x::b ** (
            allALteP,
            (
              AllCons pltex pLteAllB
            ), 
            (
              MiddleElementPermutes perm
            )
          )
        )
        

convToNat: Integer -> Nat
convToNat s = the Nat (cast s)

main : IO ()
main = do
    putStrLn "Please type a space-separated list of natural numbers: "
    csv <- getLine
    let numbers = map (fromMaybe 0 . parseInteger) (words csv) 
    -- --now you just need to sort them with a funct that goes from List Nat -> List Nat 
    let (sorted_numbers ** (_, _)) = insSort (map (convToNat . fromMaybe 0 . parseInteger) (words csv) )
    putStrLn "After sorting, the nats are: "
    print sorted_numbers
    --   putStrLn ""
    --   --or if you want to make them space separated as well
    --   -- putStrLn $ concat $ intersperse " " (map convToString sorted_numbers)
    putStrLn ""
  
  