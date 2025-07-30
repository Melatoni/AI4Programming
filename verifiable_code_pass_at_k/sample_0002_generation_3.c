// Task ID: 2
// Generation: 3

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled for parameters.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax '..'.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic TupleListProperties {
    logic integer tuple_list_size_C; // Size of a tuple list (column count)
    logic integer tuple_list_size_R; // Size of a tuple list (row count)

    // Helper to get an element from a tuple list
    logic integer get_element(int* list, integer row, integer col, integer num_cols)
      reads list[0..row * num_cols + col];
    
    axiom get_element_def:
      \forall int* list, integer row, integer col, integer num_cols;
        row >= 0 && col >= 0 && row * num_cols + col < tuple_list_size_R * tuple_list_size_C ==>
          get_element(list, row, col, num_cols) == list[row * num_cols + col];

    // Predicate to check if a tuple (row) exists in a list
    // A tuple is considered to exist if all its elements match
    predicate tuple_exists_in_list(int* list, integer list_rows, integer list_cols, int* tuple_to_find, integer tuple_cols) =
      \exists integer i; 0 <= i < list_rows &&
      (\forall integer j; 0 <= j < list_cols && j < tuple_cols ==>
        get_element(list, i, j, list_cols) == get_element(tuple_to_find, 0, j, tuple_cols)
      );

    // Predicate to check if a tuple (row) in list1 is similar to a tuple (row) in list2
    // A tuple from list1 is similar to a tuple from list2 if all their elements are equal,
    // considering the minimum of their column counts.
    predicate tuples_are_similar(int* list1, integer row1, integer col1_count,
                                 int* list2, integer row2, integer col2_count) =
      \forall integer k; 0 <= k < col1_count && k < col2_count ==>
        get_element(list1, row1, k, col1_count) == get_element(list2, row2, k, col2_count);

    // Recursive logic to count similar elements
    // This counts how many tuples from list1 have a similar tuple in list2
    logic integer count_similar_recursive(int* list1, integer rows1, integer cols1,
                                          int* list2, integer rows2, integer cols2,
                                          integer current_row1);

    axiom count_similar_recursive_base:
      \forall int* list1, integer rows1, integer cols1, int* list2, integer rows2, integer cols2;
        count_similar_recursive(list1, rows1, cols1, list2, rows2, cols2, rows1) == 0;

    axiom count_similar_recursive_step:
      \forall int* list1, integer rows1, integer cols1, int* list2, integer rows2, integer cols2, integer current_row1;
        0 <= current_row1 < rows1 ==>
          count_similar_recursive(list1, rows1, cols1, list2, rows2, cols2, current_row1) ==
          (if (\exists integer j; 0 <= j < rows2 &&
                  tuples_are_similar(list1, current_row1, cols1, list2, j, cols2))
           then 1
           else 0) + count_similar_recursive(list1, rows1, cols1, list2, rows2, cols2, current_row1 + 1);

    // Helper axiom for the total count of similar elements
    // This is the total number of distinct similar tuples found.
    logic integer total_similar_elements_count(int* list1, integer rows1, integer cols1,
                                               int* list2, integer rows2, integer cols2) =
      count_similar_recursive(list1, rows1, cols1, list2, rows2, cols2, 0);
  }
*/

/*@
  requires rows1 >= 0 && cols1 >= 0;
  requires rows2 >= 0 && cols2 >= 0;

  // Prevent potential out-of-bounds access for empty lists if they were dereferenced
  // (though the logic handles empty lists, this is for safety if pointers are used)
  requires \valid_read_range(list1, 0, rows1 * cols1 - 1) || (rows1 == 0 || cols1 == 0);
  requires \valid_read_range(list2, 0, rows2 * cols2 - 1) || (rows2 == 0 || cols2 == 0);

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like return.
  // The function returns 1 if there's at least one similar tuple, 0 otherwise.
  ensures (\exists integer i; 0 <= i < rows1 &&
           (\exists integer j; 0 <= j < rows2 &&
             (\forall integer k; 0 <= k < cols1 && k < cols2 ==>
               get_element(list1, i, k, cols1) == get_element(list2, j, k, cols2)
             )
           )
          ) <==> (result == 1);
*/
int find_similar_elements(int* list1, int rows1, int cols1,
                          int* list2, int rows2, int cols2) {
    /*@
      loop invariant 0 <= i <= rows1;
      loop invariant \forall integer p; 0 <= p < i ==>
        (found == 1 ==> (\exists integer j; 0 <= j < rows2 &&
                               (\forall integer k; 0 <= k < cols1 && k < cols2 ==>
                                 get_element(list1, p, k, cols1) == get_element(list2, j, k, cols2)
                               ));
         found == 0 ==> !(\exists integer q; 0 <= q < p &&
                                  (\exists integer j; 0 <= j < rows2 &&
                                    (\forall integer k; 0 <= k < cols1 && k < cols2 ==>
                                      get_element(list1, q, k, cols1) == get_element(list2, j, k, cols2)
                                    )
                                  )
                                )
        );
      loop invariant found == 0 || found == 1; // found is a boolean-like flag
      loop assigns i, found;
      loop variant rows1 - i;
    */
    for (int i = 0; i < rows1; i++) {
        int found_current_tuple = 0; // Rule I.2: Use int for boolean.
        /*@
          loop invariant 0 <= j <= rows2;
          loop invariant \forall integer q; 0 <= q < j ==>
            (found_current_tuple == 1 ==> (\forall integer k; 0 <= k < cols1 && k < cols2 ==>
                                           get_element(list1, i, k, cols1) == get_element(list2, q, k, cols2)
                                          );
             found_current_tuple == 0 ==> !(\exists integer l; 0 <= l < q &&
                                                (\forall integer k; 0 <= k < cols1 && k < cols2 ==>
                                                  get_element(list1, i, k, cols1) == get_element(list2, l, k, cols2)
                                                )
                                              )
            );
          loop invariant found_current_tuple == 0 || found_current_tuple == 1;
          loop assigns j, found_current_tuple;
          loop variant rows2 - j;
        */
        for (int j = 0; j < rows2; j++) {
            int is_similar = 1; // Assume similar initially
            /*@
              loop invariant 0 <= k <= cols1 && 0 <= k <= cols2;
              loop invariant \forall integer p; 0 <= p < k ==>
                (is_similar == 0 ==> get_element(list1, i, p, cols1) != get_element(list2, j, p, cols2));
              loop invariant is_similar == 0 || is_similar == 1;
              loop assigns k, is_similar;
              loop variant (cols1 < cols2 ? cols1 : cols2) - k;
            */
            for (int k = 0; k < cols1 && k < cols2; k++) {
                if (list1[i * cols1 + k] != list2[j * cols2 + k]) {
                    is_similar = 0;
                    break;
                }
            }
            if (is_similar == 1) {
                found_current_tuple = 1;
                break;
            }
        }
        if (found_current_tuple == 1) {
            return 1; // Found at least one similar pair
        }
    }
    return 0; // No similar elements found
}
