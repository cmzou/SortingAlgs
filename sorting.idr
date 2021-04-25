import Data.So
import Data.Vect
import Data.String
import Data.List.Views

--  -------------------- SETUP --------------------

-- -------------------- Data Types --------------------

-- Type that indicates a given list A starts with a given list B 
data IsHead : List e1 -> List e2 -> Type where
    HeadList : IsHead (x::rest1) (x::rest2)

--  Type that indicates two numbers are equal
data EqNat : (num1 : e) -> (num2 : e) -> Type where
    Same:
        (a: e) -> (b: e) -> EqNat a b

-- Type that indicates two lists are permutations of one another
data ListPermutation : List a -> List a -> Type where
    NilPermutesNil: ListPermutation Nil Nil
    SameHeadPermutes:
        ListPermutation a b -> ListPermutation (x::a) (x::b)
    EqualHeadPermutes:
        ListPermutation a b -> (EqNat c d) -> ListPermutation (c::a) (d::b)
    SameFirstTwoPermutes: ListPermutation(x::y::a) (y::x::a)
    MiddleElementPermutes:
        ListPermutation (a++b) d -> ListPermutation (a++x::b) (x::d)
    TransitivePermutation:
        ListPermutation a b -> ListPermutation b c -> ListPermutation a c
    ConcatentationPermutes : ListPermutation a b -> ListPermutation c d -> ListPermutation (a ++ c) (b ++ d)
    
-- Type that indicates a function applies to all elements in a list
data All: (a -> Type) -> List a -> Type where 
    AllNil: All p []
    AllCons: p x -> All p xs -> All p (x::xs)

-- Sorted Data Type
data Sorted: (lst: List Nat) -> Type where
    NilSorted: Sorted(Nil)
    SingletonSorted: (element: Nat) -> Sorted(element::Nil)
    SortedCons: Sorted xs -> All (\x => y `LTE` x) xs -> Sorted (y::xs)
    SortedAppend: (Sorted xs) -> (Sorted ys) -> (z: Nat) -> (All (\x => x `LTE` z) xs) -> (All (\x => z `LTE` x) ys) -> Sorted (xs++z::ys)

    
-- -------------------- Helper Proofs --------------------
-- Function that returns a proof that either x <= y or y <= x. Can define either for int or for nat (nat easier)
IsLte : Ord e => (x:e) -> (y:e) -> Type
IsLte x y = So (x <= y)
mkIsLte : Ord e => (x:e) -> (y:e) -> Maybe (IsLte x y)
mkIsLte x y =
  case choose (x <= y) of 
    Left proofXLteY =>
      Just proofXLteY
    Right proofNotXLteY =>
      Nothing
  
-- Transitivity Proof
transPfHelper : (w : LTE left right) -> (x : LTE right k) -> LTE left k
transPfHelper LTEZero LTEZero = LTEZero
transPfHelper LTEZero (LTESucc x) = LTEZero
transPfHelper (LTESucc y) (LTESucc x) = LTESucc (transPfHelper y x)

transPf :(x,y,z : Nat) ->  LTE x y -> LTE y z -> LTE x z
transPf Z Z z LTEZero LTEZero = LTEZero
transPf Z (S left) (S right) LTEZero (LTESucc x) = LTEZero
transPf (S left) (S right) (S k) (LTESucc w) (LTESucc x) =
  LTESucc (transPfHelper w x)

-- Reflexivity/anti-symmetry Proof
reflPf : (x,y : Nat) -> Either (LTE x y) (LTE y x)
reflPf Z y = Left LTEZero
reflPf x Z = Right LTEZero
reflPf (S k) (S j) with (reflPf k j)
  reflPf (S k) (S j) | (Left l) = Left (LTESucc l)
  reflPf (S k) (S j) | (Right r) = Right (LTESucc r)



-- -------------------- Proofs of Permutation Properties --------------------

listPermutationReflexive: ListPermutation xs xs
listPermutationReflexive {xs = []} = NilPermutesNil
listPermutationReflexive {xs = x :: xs} = SameHeadPermutes (listPermutationReflexive {xs=xs})

listPermutationSymmetric: ListPermutation xs ys -> ListPermutation ys xs
listPermutationSymmetric NilPermutesNil = NilPermutesNil
listPermutationSymmetric (SameHeadPermutes x) = SameHeadPermutes (listPermutationSymmetric  x)
listPermutationSymmetric SameFirstTwoPermutes = SameFirstTwoPermutes
listPermutationSymmetric (TransitivePermutation x y) = TransitivePermutation (listPermutationSymmetric y) (listPermutationSymmetric x)
listPermutationSymmetric (ConcatentationPermutes a b) = (ConcatentationPermutes (listPermutationSymmetric a) (listPermutationSymmetric b))

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
  

-- -------------------- Proofs of "All" Properties --------------------
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


-- -------------------- Merge Sort --------------------

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

-- Adapted from Type-driven Development with Idris - Edwin Brady, Chapter 10
mergeSort: (xs: List Nat) -> (ys: List Nat ** (Sorted ys, ListPermutation xs ys))
mergeSort input with (splitRec input)
      mergeSort [] | SplitRecNil = ([] ** (NilSorted, listPermutationReflexive))
      mergeSort [x] | SplitRecOne = ([x] ** ((SortedCons NilSorted AllNil), listPermutationReflexive))
      mergeSort (left ++ right) | (SplitRecPair lrec rrec) = 
        let (left_side ** (left_ord, left_perm)) = (mergeSort left | lrec) in
        let (right_side ** (right_ord, right_perm)) = (mergeSort right | rrec) in
        let (total_merge ** (total_ord, total_perm)) = mergeLists left_side left_ord right_side right_ord in
        (total_merge ** (total_ord, TransitivePermutation (ConcatentationPermutes left_perm right_perm) total_perm))


-- -------------------- Insertion Sort --------------------

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

-- Adapted from Type-driven Development with Idris - Edwin Brady, Chapter 3
insSort : (xs : List Nat) -> 
          (ys : List Nat ** (Sorted ys, ListPermutation xs ys))
insSort [] = ([] ** (NilSorted, NilPermutesNil))
insSort (x::xs) = 
  let (xsNew ** (xs_ord, xs_perm)) = insSort xs in
  let (total_list ** (total_ord, total_perm)) = insertSingleElement xsNew xs_ord x in
  let total_perm_rev = listPermutationSymmetric total_perm in
  let match = TransitivePermutation (SameHeadPermutes xs_perm) total_perm_rev in
  (total_list ** (total_ord, match))


-- -------------------- Quicksort --------------------

partition: (p: Nat) -> (xs: List Nat) -> (as : List Nat ** 
  bs : List Nat **
  ( (All (\x => LTE x p) as)
  , (All (\x => LTE p x) bs)
  , ListPermutation (as ++ bs) xs
  )
)
partition p [] = ([] ** [] ** (AllNil,AllNil,NilPermutesNil))
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
                SameHeadPermutes perm
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

quickSort : (xs : List Nat) -> 
  (ys : List Nat ** (Sorted ys, ListPermutation xs ys))
quickSort [] = ([] ** (NilSorted, NilPermutesNil))
quickSort [x] = ([x] ** ((SingletonSorted x), listPermutationReflexive))
quickSort (x::xs) =
    let (a ** b ** (altex, xlteb, perm)) = partition x xs in
    let (asorted ** (sorteda, apermasorted)) = quickSort a in
    let (bsorted ** (sortedb, bpermbsorted)) = quickSort b in
    (
        (asorted ++ x::bsorted) **
        (
            (
                SortedAppend
                sorteda
                sortedb
                x
                (allSurvivesPermutation altex apermasorted)
                (allSurvivesPermutation xlteb bpermbsorted)
            ),
            (
                listPermutationSymmetric
                (
                    MiddleElementPermutes
                    (
                        listPermutationSymmetric
                        (
                            TransitivePermutation
                            (listPermutationSymmetric perm)
                            (ConcatentationPermutes apermasorted bpermbsorted)
                        )
                    )
                )
            )
        )
    )

-- -------------------- Permutation Checker --------------------

findMatch: (Eq e) => (x: e) -> (xs : List e) -> Maybe (zs : List e ** (ListPermutation (x::zs) xs))
findMatch x [] = Nothing
findMatch a (x::xs) =
    case (a == x) of
        True =>
            Just (
                xs ** (EqualHeadPermutes (listPermutationReflexive) (Same a x))
                -- Maybe do something like this??
                -- https://stackoverflow.com/questions/46853917/idris-proving-equality-of-two-numbers
            )
        False =>
            let res = findMatch a xs in
                case res of
                    Just (zs ** azspermxs) => -- a:zs = xs => x::a::zs = x::xs
                        Just ( 
                            (x::zs) ** (
                                (
                                    TransitivePermutation
                                    SameFirstTwoPermutes
                                    (SameHeadPermutes azspermxs)
                                )
                            )
                        )
                    Nothing =>
                        Nothing

permutationChecker: (Eq e) => (xs: List e) -> (ys: List e) -> Maybe (ListPermutation xs ys)
permutationChecker [] [] = Just NilPermutesNil
permutationChecker [] _ = Nothing
permutationChecker _ [] = Nothing
permutationChecker (x::xs) ys =
    let match = findMatch x ys in
        case match of 
            Just (zs ** xzspermys) => -- xzpermys: ListPermutation x::zs ys
                let recurse = permutationChecker xs zs in
                    case recurse of
                        Just xspermzs => -- ListPermutation xs zs
                            -- x::xs = x::zs and x::zs = ys => x::xs == ys
                            Just -- ListPermutation (x :: xs) ys
                                (
                                    TransitivePermutation
                                    (SameHeadPermutes xspermzs)
                                    xzspermys
                                ) 
                        Nothing =>
                            Nothing
            Nothing =>
                Nothing


-- -------------------- IO --------------------

getSortResult: ( ys : List Nat ** (Sorted ys, ListPermutation xs ys)) -> List Nat
getSortResult (x ** _) = x 

convToNat: Integer -> Nat
convToNat s = the Nat (cast s)

runPerm: IO()
runPerm = do
    putStrLn "Please type a space-separated list of natural numbers or symbols (List 1): "
    first <- getLine
    let firstnum = (words first)

    putStrLn "Please type a space-separated list of natural numbers or symbols (List 2): "
    second <- getLine
    let secondnum = (words second)        
    let answer = permutationChecker firstnum secondnum
    case answer of
        Just _ =>
            putStrLn "Lists Permute :)"
        Nothing => 
            putStrLn "List Do Not Permute :("

runSort: IO()
runSort = 
    do
        putStrLn "Enter 1 for Merge Sort, 2 for Insertion Sort, 3 for Quicksort"
        res <- getLine
        let response = (fromMaybe 1 . parseInteger) res
        case response of
            1 =>
                do
                    putStrLn "Please type a space-separated list of natural numbers: "
                    csv <- getLine
                    print (getSortResult (mergeSort (map (convToNat . fromMaybe 0 . parseInteger) (words csv))))
            2 =>
                do
                    putStrLn "Please type a space-separated list of natural numbers: "
                    csv <- getLine
                    print (getSortResult (mergeSort (map (convToNat . fromMaybe 0 . parseInteger) (words csv))))        
            _ =>
                do
                    putStrLn "Please type a space-separated list of natural numbers: "
                    csv <- getLine
                    print (getSortResult (mergeSort (map (convToNat . fromMaybe 0 . parseInteger) (words csv))))

        putStrLn ""
    
main : IO ()
main = do
        putStrLn "Enter 1 to sort a list, 2 to verify list permutations, 3 to quit"
        res <- getLine
        let response = (fromMaybe 1 . parseInteger) res
        case response of
            1 =>
                do
                    
                    runSort
                    main
            2 =>
                do
                    runPerm
                    main
            _ => putStrLn "Bye bye"

        putStrLn ""