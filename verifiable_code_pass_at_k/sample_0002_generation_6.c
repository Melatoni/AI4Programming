// Task ID: 2
// Generation: 6

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule I.1: No standard libraries.
  // Rule II.5: Prevent runtime errors.
  // Assume tuple elements are non-negative and within int range.
  // Max size for arrays to prevent overflow in indexing.
  requires 0 <= size1 <= 10000;
  requires 0 <= size2 <= 10000;

  // Rule I.3: Array parameters decay to pointers.
  // The type of `tuple_list1` is `int (*)[2]` because `int tuple_list1[][2]` decays.
  // The type of `tuple_list2` is `int (*)[2]` because `int tuple_list2[][2]` decays.
  assigns \nothing;

  // Axiomatic block for recursive logic to define "contains" property.
  // Rule II.1: Use recursive logic for complex properties.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.1: No C-style ternary in ACSL.
*/
/*@
  axiomatic TupleListContains {
    logic boolean contains_tuple(int (*list)[2], int size, int t1, int t2) reads list[0..size-1];

    axiom contains_tuple_base:
      \forall int (*list)[2], int t1, int t2;
        contains_tuple(list, 0, t1, t2) == \false;

    axiom contains_tuple_recursive:
      \forall int (*list)[2], int size, int t1, int t2;
        size > 0 ==>
        (contains_tuple(list, size, t1, t2) ==
         (if (list[size-1][0] == t1 && list[size-1][1] == t2)
          then \true
          else contains_tuple(list, size - 1, t1, t2)));

    // Rule II.2: Helper axioms are CRITICAL for the prover.
    // This helper axiom states that if a tuple is in a sublist, it's also in the full list.
    axiom contains_tuple_helper_sublist:
      \forall int (*list)[2], integer i, integer size, int t1, int t2;
        0 <= i < size ==>
        contains_tuple(list, i, t1, t2) ==> contains_tuple(list, size, t1, t2);

    // This helper axiom states that if a tuple is not in a larger list, it's not in any sublist.
    axiom contains_tuple_helper_no_sublist:
      \forall int (*list)[2], integer i, integer size, int t1, int t2;
        0 <= i < size ==>
        !contains_tuple(list, size, t1, t2) ==> !contains_tuple(list, i, t1, t2);
  }
*/

/*@
  // Rule II.3: Use logical equivalence for boolean-like functions.
  ensures (\forall integer i; 0 <= i < size1 ==>
           (\exists integer j; 0 <= j < size2 &&
            tuple_list1[i][0] == tuple_list2[j][0] &&
            tuple_list1[i][1] == tuple_list2[j][1])
          ) <==> (\result == 1);
*/
int find_similar_elements(int tuple_list1[][2], int size1, int tuple_list2[][2], int size2) {
    /*@
      loop invariant 0 <= i <= size1;
      loop invariant \forall integer k; 0 <= k < i ==>
                       contains_tuple(tuple_list2, size2, tuple_list1[k][0], tuple_list1[k][1]);
      loop assigns i;
      loop variant size1 - i;
    */
    for (int i = 0; i < size1; i++) {
        int found_in_list2 = 0; // Rule I.2: Use int for boolean.
        /*@
          loop invariant 0 <= j <= size2;
          loop invariant \forall integer l; 0 <= l < j ==>
                           !(tuple_list1[i][0] == tuple_list2[l][0] &&
                             tuple_list1[i][1] == tuple_list2[l][1]);
          loop invariant found_in_list2 == 0; // This loop should only set it to 1 and break.
          loop assigns j, found_in_list2;
          loop variant size2 - j;
        */
        for (int j = 0; j < size2; j++) {
            if (tuple_list1[i][0] == tuple_list2[j][0] && tuple_list1[i][1] == tuple_list2[j][1]) {
                found_in_list2 = 1;
                // Rule III.4: No stray semicolons.
                break;
            }
        }
        if (found_in_list2 == 0) {
            return 0; // Not all elements from list1 are found in list2.
        }
    }
    return 1; // All elements from list1 are found in list2.
}
