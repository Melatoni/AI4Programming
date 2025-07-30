// Task ID: 2
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay (handled in function signature).
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic TupleListLogic {
    // Defines a tuple element as present in a list at a specific index.
    // list: The tuple list.
    // row: The row index of the tuple.
    // col: The column index within the tuple (0 for first element, 1 for second).
    // val: The value to check for.
    logic boolean is_tuple_element_at(int **list, int row, int col, int val) reads list;
    axiom is_tuple_element_at_def{L}(int **list, int row, int col, int val) =
      list[row][col] == val;

    // Defines whether a specific value 'val' exists in the first column of any tuple
    // within the first 'n' tuples of the list.
    // Used to check for presence of first elements of tuples.
    logic boolean exists_first_element(int **list, int n, int val) reads list;
    axiom exists_first_element_base{L}(int **list, int n, int val) =
      (n <= 0) ==> !exists_first_element(list, n, val);
    axiom exists_first_element_rec{L}(int **list, int n, int val) =
      (n > 0) ==> (is_tuple_element_at(list, n - 1, 0, val) || exists_first_element(list, n - 1, val));

    // Defines whether a specific value 'val' exists in the second column of any tuple
    // within the first 'n' tuples of the list.
    // Used to check for presence of second elements of tuples.
    logic boolean exists_second_element(int **list, int n, int val) reads list;
    axiom exists_second_element_base{L}(int **list, int n, int val) =
      (n <= 0) ==> !exists_second_element(list, n, val);
    axiom exists_second_element_rec{L}(int **list, int n, int val) =
      (n > 0) ==> (is_tuple_element_at(list, n - 1, 1, val) || exists_second_element(list, n - 1, val));

    // Defines whether a tuple (val1, val2) exists in the first 'n' tuples of list.
    logic boolean exists_tuple(int **list, int n, int val1, int val2) reads list;
    axiom exists_tuple_base{L}(int **list, int n, int val1, int val2) =
      (n <= 0) ==> !exists_tuple(list, n, val1, val2);
    axiom exists_tuple_rec{L}(int **list, int n, int val1, int val2) =
      (n > 0) ==> (is_tuple_element_at(list, n - 1, 0, val1) && is_tuple_element_at(list, n - 1, 1, val2) || exists_tuple(list, n - 1, val1, val2));
  }
*/

/*@
  requires \valid_read(list1) && \valid_read(list2);
  requires n1 >= 0 && n2 >= 0;

  // Each element of list1 and list2 must be a valid pointer to an array of 2 integers.
  // This is crucial for accessing list1[i][0] and list1[i][1].
  requires \for_all integer i; 0 <= i < n1 ==> \valid_read(list1[i] + (0..1));
  requires \for_all integer i; 0 <= i < n2 ==> \valid_read(list2[i] + (0..1));

  // The function returns 1 if there's at least one tuple (v1, v2) that exists in both list1 and list2.
  // It returns 0 otherwise.
  ensures (\exists integer i, j;
             0 <= i < n1 && 0 <= j < n2 &&
             list1[i][0] == list2[j][0] && list1[i][1] == list2[j][1]) <==> (\result == 1);
  assigns \nothing;
*/
int find_similar_tuples(int **list1, int n1, int **list2, int n2) {
    /*@
      loop invariant 0 <= i <= n1;
      // If a similar tuple has been found, found_similar is 1.
      // If found_similar is 0, no similar tuple has been found yet among list1[0..i-1] and list2[0..n2-1].
      loop invariant (\exists integer k, l;
                        0 <= k < i && 0 <= l < n2 &&
                        list1[k][0] == list2[l][0] && list1[k][1] == list2[l][1]) <==> (\result == 1);
      loop assigns i;
      loop variant n1 - i;
    */
    for (int i = 0; i < n1; i++) {
        int val1_1 = list1[i][0];
        int val1_2 = list1[i][1];

        /*@
          loop invariant 0 <= j <= n2;
          // If a similar tuple involving list1[i] has been found, found_similar is 1.
          // If found_similar is 0, list1[i] has no match in list2[0..j-1].
          loop invariant (\exists integer l;
                            0 <= l < j &&
                            val1_1 == list2[l][0] && val1_2 == list2[l][1]) <==> (\result == 1);
          loop assigns j;
          loop variant n2 - j;
        */
        for (int j = 0; j < n2; j++) {
            int val2_1 = list2[j][0];
            int val2_2 = list2[j][1];

            if (val1_1 == val2_1 && val1_2 == val2_2) {
                return 1; // Found a similar tuple
            }
        }
    }
    return 0; // No similar tuples found
}

// Note: This function focuses on finding *any* similar tuple.
// If the problem implies finding common elements *within* tuples (e.g., if (1,5) and (5,8) means 5 is common),
// the logic would be different. Based on "similar elements from the given two tuple lists",
// it is interpreted as finding identical tuples (pairs).
