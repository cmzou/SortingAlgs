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
sortedHelper: (xs: List Nat)

quickSort : (xs : List Nat) -> 
  (ys : List Nat ** (Sorted ys, ListPermutation xs ys))
quickSort [] = ([] ** (NilSorted, NilPermutesNil))
quickSort (x::xs) =
    let (a ** b ** (altex, xlteb, perm)) = partition x xs in
    let (asorted ** (sorteda, apermasorted)) = quickSort a in
    let (bsorted ** (sortedb, bpermbsorted)) = quickSort b in
    (
        (asorted ++ bsorted) **
        (
            (
                ?sorted
            ),
            (
                TransitivePermutation
                (listPermutationSymmetric perm)
                (ConcatentationPermutes apermasorted bpermbsorted)
            )
        )
    )

    -- TransitivePermutation:
    -- ListPermutation a b -> ListPermutation b c -> ListPermutation a c
    -- listPermutationBackAppend: ListPermutation xs xs' -> ListPermutation (xs ++ ys) (xs' ++ ys)
