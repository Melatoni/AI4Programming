// Task ID: 2
// Generation: 0

/*@
  // Rule II.1: Define recursive logic function for tuple equality.
  axiomatic Tuple {
    logic boolean tuple_equal(int[] t1, int[] t2, int len);

    // Base case: empty tuples are equal.
    axiom tuple_equal_base:
      \forall int[] t1, t2, len; len <= 0 ==> tuple_equal(t1, t2, len);

    // Recursive step: tuples are equal if their last elements are equal and the rest are equal.
    axiom tuple_equal_recursive:
      \forall int[] t1, t2, len; len > 0 ==>
        (tuple_equal(t1, t2, len) <==> (t1[len - 1] == t2[len - 1] && tuple_equal(t1, t2, len - 1)));
  }
*/

/*@
  // Rule II.1: Define recursive logic function for list element existence.
  axiomatic ListContains {
    logic boolean list_contains(int[][*] list, int list_len, int tuple_len, int[] tuple);

    // Base case: empty list does not contain any tuple.
    axiom list_contains_base:
      \forall int[][*] list, list_len, tuple_len, int[] tuple; list_len <= 0 ==> !list_contains(list, list_len, tuple_len, tuple);

    // Recursive step: list contains tuple if the last element is equal or the rest of the list contains it.
    axiom list_contains_recursive:
      \forall int[][*] list, list_len, tuple_len, int[] tuple; list_len > 0 ==>
        (list_contains(list, list_len, tuple_len, tuple) <==>
          (tuple_equal(list[list_len - 1], tuple, tuple_len) || list_contains(list, list_len - 1, tuple_len, tuple)));
  }
*/

/*@
  requires list1_len >= 0;
  requires list2_len >= 0;
  requires tuple_len >= 0;
  // Rule II.5: Prevent out-of-bounds access for list1 and list2.
  requires \forall integer i; 0 <= i < list1_len ==> \valid(list1[i] + (0..tuple_len - 1));
  requires \forall integer i; 0 <= i < list2_len ==> \valid(list2[i] + (0..tuple_len - 1));
  // Rule II.5: Prevent out-of-bounds access for common_elements array.
  requires \valid(common_elements + (0..list1_len - 1));

  assigns common_elements[0..list1_len - 1];

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The result is the number of similar elements found.
  ensures \forall integer i; 0 <= i < \result ==>
    list_contains(list2, list2_len, tuple_len, common_elements[i]) &&
    list_contains(list1, list1_len, tuple_len, common_elements[i]);

  ensures \forall integer i,j; 0 <= i < j < \result ==>
    !tuple_equal(common_elements[i], common_elements[j], tuple_len);

  ensures \forall integer i; 0 <= i < list1_len ==>
    (list_contains(list2, list2_len, tuple_len, list1[i]) <==>
     (\exists integer k; 0 <= k < \result && tuple_equal(common_elements[k], list1[i], tuple_len)));

  ensures \result >= 0 && \result <= list1_len;
*/
int find_similar_elements(int (*list1)[], int list1_len, int (*list2)[], int list2_len, int tuple_len, int (*common_elements)[]) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= list1_len;
      loop invariant 0 <= count <= i;
      // Rule II.4: Invariant for common_elements content.
      loop invariant \forall integer k; 0 <= k < count ==>
        list_contains(list2, list2_len, tuple_len, common_elements[k]) &&
        list_contains(list1, i, tuple_len, common_elements[k]);
      // Rule II.4: Invariant for common_elements uniqueness.
      loop invariant \forall integer k, l; 0 <= k < l < count ==>
        !tuple_equal(common_elements[k], common_elements[l], tuple_len);
      // Rule II.4: Invariant for completeness of common_elements up to i.
      loop invariant \forall integer k; 0 <= k < i ==>
        (list_contains(list2, list2_len, tuple_len, list1[k]) <==>
         (\exists integer m; 0 <= m < count && tuple_equal(common_elements[m], list1[k], tuple_len)));

      loop assigns i, count, common_elements[0..list1_len-1];
      loop variant list1_len - i;
    */
    for (int i = 0; i < list1_len; i++) {
        int current_tuple[tuple_len]; // Temporary array for current tuple from list1
        /*@
          loop invariant 0 <= j <= tuple_len;
          loop invariant \forall integer k; 0 <= k < j ==> current_tuple[k] == list1[i][k];
          loop assigns j, current_tuple[0..tuple_len-1];
          loop variant tuple_len - j;
        */
        for (int j = 0; j < tuple_len; j++) {
            current_tuple[j] = list1[i][j];
        }

        int found_in_list2 = 0;
        /*@
          loop invariant 0 <= j <= list2_len;
          loop invariant found_in_list2 == (list_contains(list2, j, tuple_len, current_tuple));
          loop assigns j, found_in_list2;
          loop variant list2_len - j;
        */
        for (int j = 0; j < list2_len; j++) {
            if (tuple_equal(list2[j], current_tuple, tuple_len)) {
                found_in_list2 = 1;
                break;
            }
        }

        if (found_in_list2 == 1) {
            // Check if this tuple is already in common_elements to avoid duplicates
            int already_added = 0;
            /*@
              loop invariant 0 <= k <= count;
              loop invariant already_added == (\exists integer m; 0 <= m < k && tuple_equal(common_elements[m], current_tuple, tuple_len));
              loop assigns k, already_added;
              loop variant count - k;
            */
            for (int k = 0; k < count; k++) {
                if (tuple_equal(common_elements[k], current_tuple, tuple_len)) {
                    already_added = 1;
                    break;
                }
            }

            if (already_added == 0) {
                /*@
                  loop invariant 0 <= k <= tuple_len;
                  loop invariant \forall integer m; 0 <= m < k ==> common_elements[count][m] == current_tuple[m];
                  loop assigns k, common_elements[count][0..tuple_len-1];
                  loop variant tuple_len - k;
                */
                for (int k = 0; k < tuple_len; k++) {
                    common_elements[count][k] = current_tuple[k];
                }
                count++;
            }
        }
    }
    return count;
}
