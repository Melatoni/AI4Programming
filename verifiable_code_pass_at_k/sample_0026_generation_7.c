// Task ID: 26
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule I.3: Array pointer decay for consistency.

  axiomatic TupleList {
    logic integer get_first_element(int* tuple);
    logic integer get_second_element(int* tuple);

    axiom get_first_element_def:
      \forall int* tuple; get_first_element(tuple) == tuple[0];

    axiom get_second_element_def:
      \forall int* tuple; get_second_element(tuple) == tuple[1];

    // Recursive logic to check if all k elements are present in the list.
    // This logic function checks if a specific 'k_val' is present in the first 'count' tuples.
    logic boolean is_k_present_in_list(int* tuple_list[], integer list_size, integer tuple_size, integer k_val, integer count);

    axiom is_k_present_in_list_base_empty:
      \forall int* tuple_list[], integer list_size, integer tuple_size, integer k_val;
        is_k_present_in_list(tuple_list, list_size, tuple_size, k_val, 0) == \false;

    axiom is_k_present_in_list_base_found:
      \forall int* tuple_list[], integer list_size, integer tuple_size, integer k_val, integer count;
        0 < count <= list_size && (get_first_element(tuple_list[count - 1]) == k_val || get_second_element(tuple_list[count - 1]) == k_val)
        ==> is_k_present_in_list(tuple_list, list_size, tuple_size, k_val, count) == \true;

    axiom is_k_present_in_list_recursive_not_found:
      \forall int* tuple_list[], integer list_size, integer tuple_size, integer k_val, integer count;
        0 < count <= list_size && !(get_first_element(tuple_list[count - 1]) == k_val || get_second_element(tuple_list[count - 1]) == k_val)
        ==> is_k_present_in_list(tuple_list, list_size, tuple_size, k_val, count) == is_k_present_in_list(tuple_list, list_size, tuple_size, k_val, count - 1);

    // This logic function checks if all elements from 0 to k-1 are present in the given list.
    logic boolean all_k_elements_present(int* tuple_list[], integer list_size, integer tuple_size, integer k);

    axiom all_k_elements_present_base_empty_k:
      \forall int* tuple_list[], integer list_size, integer tuple_size;
        all_k_elements_present(tuple_list, list_size, tuple_size, 0) == \true;

    axiom all_k_elements_present_recursive:
      \forall int* tuple_list[], integer list_size, integer tuple_size, integer k;
        k > 0
        ==> all_k_elements_present(tuple_list, list_size, tuple_size, k) == (is_k_present_in_list(tuple_list, list_size, tuple_size, k - 1, list_size) && all_k_elements_present(tuple_list, list_size, tuple_size, k - 1));
  }
*/

/*@
  requires list_size >= 0;
  requires tuple_size == 2; // Each tuple is an array of 2 integers.
  requires k >= 0;
  requires \valid_read(tuple_list + (0..list_size-1)); // Ensure tuple_list is readable up to list_size - 1
  requires \forall integer i; 0 <= i < list_size ==> \valid_read(tuple_list[i] + (0..tuple_size-1)); // Ensure each tuple is readable

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  ensures (all_k_elements_present(tuple_list, list_size, tuple_size, k)) <==> (esult == 1);
*/
int has_all_k_elements(int* tuple_list[], int list_size, int tuple_size, int k) { // Rule I.2: Uses int for boolean
    /*@
      loop invariant 0 <= i <= k;
      // Rule II.4: Invariant for the loop.
      loop invariant \forall integer j; 0 <= j < i ==> is_k_present_in_list(tuple_list, list_size, tuple_size, j, list_size);
      loop assigns i;
      // Rule II.4: Loop variant for termination.
      loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        int found_i = 0; // Rule I.2: Uses int for boolean
        /*@
          loop invariant 0 <= j <= list_size;
          // Rule II.4: Invariant for the inner loop.
          loop invariant found_i == 1 || (\forall integer l; 0 <= l < j ==> !(get_first_element(tuple_list[l]) == i || get_second_element(tuple_list[l]) == i));
          loop assigns j, found_i;
          // Rule II.4: Loop variant for termination.
          loop variant list_size - j;
        */
        for (int j = 0; j < list_size; j++) {
            // Rule II.5: No overflow issue here as tuple elements are just compared.
            if (tuple_list[j][0] == i || tuple_list[j][1] == i) {
                found_i = 1;
                break;
            }
        }
        if (found_i == 0) {
            return 0; // Corresponds to the 'false' case of the ensures clause.
        }
    }
    return 1; // Corresponds to the 'true' case of the ensures clause.
}
