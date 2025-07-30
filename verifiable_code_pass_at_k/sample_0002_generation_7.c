// Task ID: 2
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in logic functions.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms are CRITICAL.

  // Axiomatic block to define properties of tuples and lists of tuples.
  axiomatic TupleProperties {

    // Define a tuple as a pair of integers.
    logic int tuple_first(int* t);
    logic int tuple_second(int* t);

    // Axioms for tuple access (assuming t is an array of size 2)
    axiom tuple_first_def: 
      \forall int* t; tuple_first(t) == t[0];
    axiom tuple_second_def:
      \forall int* t; tuple_second(t) == t[1];

    // Recursive logic function to check if a tuple exists in a list.
    // list: The array representing the list of tuples.
    // list_len: Current length of the list being checked.
    // target_t: The tuple we are looking for.
    logic int tuple_in_list{L}(int (*list)[2], int list_len, int* target_t);

    // Base case: An empty list does not contain any tuple.
    axiom tuple_in_list_base:
      \forall int* target_t; tuple_in_list(list, 0, target_t) == 0; // 0 for false

    // Recursive case: Check current element or recurse on the rest of the list.
    axiom tuple_in_list_rec:
      \forall int (*list)[2], int list_len, int* target_t;
      list_len > 0 ==>
      (tuple_in_list(list, list_len, target_t) == 
       (if (tuple_first(list[list_len - 1]) == tuple_first(target_t) &&
            tuple_second(list[list_len - 1]) == tuple_second(target_t))
        then 1 // 1 for true
        else tuple_in_list(list, list_len - 1, target_t)));

    // Helper axiom: If a tuple is in a list, and that list is a sublist of another,
    // then the tuple is also in the larger list.
    // This helps the prover with quantifiers and sub-array properties.
    axiom tuple_in_list_sublist:
      \forall int (*list1)[2], int len1, int (*list2)[2], int len2, int* target_t;
      len1 <= len2 &&
      \forall integer i; 0 <= i < len1 ==> (list1[i][0] == list2[i][0] && list1[i][1] == list2[i][1]) ==>
      (tuple_in_list(list1, len1, target_t) == 1 ==> tuple_in_list(list2, len1, target_t) == 1);

    // Helper axiom: If a tuple is NOT in a sublist, it's NOT in the larger list (up to that sublist point).
    // This is useful for proving that an element is *not* found.
    axiom tuple_not_in_sublist:
      \forall int (*list1)[2], int len1, int (*list2)[2], int len2, int* target_t;
      len1 <= len2 &&
      \forall integer i; 0 <= i < len1 ==> (list1[i][0] == list2[i][0] && list1[i][1] == list2[i][1]) ==>
      (tuple_in_list(list1, len1, target_t) == 0 ==> tuple_in_list(list2, len1, target_t) == 0);

  }
*/

/*@
  requires list1_len >= 0;
  requires list2_len >= 0;
  requires \valid_read(list1) || list1_len == 0;
  requires \valid_read(list2) || list2_len == 0;
  
  // Ensures the output array is valid for writing up to the found_count.
  requires \valid(result_list) || result_list_max_len == 0;
  requires \valid(result_list[0..result_list_max_len-1]) || result_list_max_len == 0;

  requires result_list_max_len >= 0;

  // Rule II.5: Prevent overflow if tuple elements are large.
  // This example assumes tuple elements are small enough not to cause issues
  // with comparisons or intermediate values if they were used in arithmetic.
  // If tuple elements could be large, further requires clauses would be needed.
  // For simplicity, we assume element values do not cause overflow during comparison.

  assigns result_list[0..result_list_max_len-1], found_count;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // Specifies that found_count is the number of tuples from list1 that are also in list2,
  // and these tuples are stored in result_list.
  ensures found_count >= 0;
  ensures found_count <= list1_len;
  ensures found_count <= result_list_max_len;

  ensures \forall integer k; 0 <= k < found_count ==>
          tuple_in_list(list2, list2_len, result_list[k]) == 1;

  // Ensures that all elements in result_list are unique and come from list1.
  ensures \forall integer k1, k2; 0 <= k1 < k2 < found_count ==>
          !(result_list[k1][0] == result_list[k2][0] && result_list[k1][1] == result_list[k2][1]);

  ensures \forall integer k; 0 <= k < found_count ==>
          tuple_in_list(list1, list1_len, result_list[k]) == 1;

  // Ensures that any tuple from list1 that is also in list2 is present in result_list.
  // This is the core property of "similar elements".
  ensures \forall integer i; 0 <= i < list1_len ==>
          (tuple_in_list(list2, list2_len, list1[i]) == 1 <==>
           tuple_in_list(result_list, found_count, list1[i]) == 1);
*/
void find_similar_tuples(int (*list1)[2], int list1_len,
                         int (*list2)[2], int list2_len,
                         int (*result_list)[2], int result_list_max_len,
                         int* found_count) {
    
    *found_count = 0;

    /*@
      loop invariant 0 <= i <= list1_len;
      loop invariant 0 <= *found_count <= i;
      loop invariant *found_count <= result_list_max_len;

      // All elements added to result_list so far are from list1 and are in list2.
      loop invariant \forall integer k; 0 <= k < *found_count ==>
                     tuple_in_list(list1, i, result_list[k]) == 1 &&
                     tuple_in_list(list2, list2_len, result_list[k]) == 1;

      // All elements in result_list so far are unique.
      loop invariant \forall integer k1, k2; 0 <= k1 < k2 < *found_count ==>
                     !(result_list[k1][0] == result_list[k2][0] && result_list[k1][1] == result_list[k2][1]);

      // No tuple from list1[0..i-1] that is in list2 but not yet in result_list.
      // This ensures we don't miss any.
      loop invariant \forall integer k_list1; 0 <= k_list1 < i ==>
                     (tuple_in_list(list2, list2_len, list1[k_list1]) == 1 <==>
                      tuple_in_list(result_list, *found_count, list1[k_list1]) == 1);

      loop assigns i, *found_count, result_list[0..result_list_max_len-1];
      loop variant list1_len - i;
    */
    for (int i = 0; i < list1_len; i++) {
        int current_tuple[2] = {list1[i][0], list1[i][1]}; // Copy to avoid issues with array decay in logic func args

        // Check if current_tuple is in list2
        int in_list2 = 0;
        /*@
          loop invariant 0 <= j <= list2_len;
          loop invariant in_list2 == 1 <==> tuple_in_list(list2, j, current_tuple) == 1;
          loop assigns j, in_list2;
          loop variant list2_len - j;
        */
        for (int j = 0; j < list2_len; j++) {
            if (list2[j][0] == current_tuple[0] && list2[j][1] == current_tuple[1]) {
                in_list2 = 1;
                break;
            }
        }

        if (in_list2 == 1) {
            // Check if current_tuple is already in result_list (to ensure uniqueness)
            int already_in_result = 0;
            /*@
              loop invariant 0 <= k <= *found_count;
              loop invariant already_in_result == 1 <==> tuple_in_list(result_list, k, current_tuple) == 1;
              loop assigns k, already_in_result;
              loop variant *found_count - k;
            */
            for (int k = 0; k < *found_count; k++) {
                if (result_list[k][0] == current_tuple[0] && result_list[k][1] == current_tuple[1]) {
                    already_in_result = 1;
                    break;
                }
            }

            if (already_in_result == 0) {
                // Add to result_list if space is available
                /*@
                  requires *found_count < result_list_max_len;
                  assigns result_list[*found_count], *found_count;
                  ensures *found_count == \old(*found_count) + 1;
                  ensures result_list[\old(*found_count)][0] == current_tuple[0] &&
                          result_list[\old(*found_count)][1] == current_tuple[1];
                */
                if (*found_count < result_list_max_len) {
                    result_list[*found_count][0] = current_tuple[0];
                    result_list[*found_count][1] = current_tuple[1];
                    (*found_count)++;
                }
            }
        }
    }
}
