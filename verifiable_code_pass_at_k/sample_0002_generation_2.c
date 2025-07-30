// Task ID: 2
// Generation: 2

/*@
  // Rule II.1, II.2: Define a recursive logic function for tuple equality.
  // This is better than trying to express complex tuple comparison inline.
  axiomatic Tuple {
    logic int tuple_equals(int* t1, int* t2, int size);

    axiom tuple_equals_base:
      \forall int* t1, int* t2, int size;
        size <= 0 ==> tuple_equals(t1, t2, size) == 1; // Empty tuples are equal

    axiom tuple_equals_recursive:
      \forall int* t1, int* t2, int size;
        size > 0 ==> (tuple_equals(t1, t2, size) == (if t1[size-1] == t2[size-1] then tuple_equals(t1, t2, size-1) else 0));
  }
*/

/*@
  // Rule II.1, II.2: Define a recursive logic function to check if a tuple exists in a list.
  axiomatic TupleList {
    logic int tuple_list_contains(int** list, int list_size, int* tuple, int tuple_size);

    axiom tuple_list_contains_base:
      \forall int** list, int list_size, int* tuple, int tuple_size;
        list_size <= 0 ==> tuple_list_contains(list, list_size, tuple, tuple_size) == 0;

    axiom tuple_list_contains_recursive:
      \forall int** list, int list_size, int* tuple, int tuple_size;
        list_size > 0 ==> (tuple_list_contains(list, list_size, tuple, tuple_size) ==
                           (if tuple_equals(list[list_size-1], tuple, tuple_size) then 1 else tuple_list_contains(list, list_size-1, tuple, tuple_size)));
  }
*/

/*@
  requires list1 != \null;
  requires list2 != \null;
  requires list1_size >= 0;
  requires list2_size >= 0;
  requires tuple_size >= 0;

  // Rule I.3: Array parameters decay to pointers.
  // The 'assigns' clause should reflect this if elements within the arrays are modified.
  // Here, we are not modifying, so it's `nothing`.
  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The result is 1 if there exists at least one tuple in list1 that is also in list2.
  // The result is 0 otherwise.
  ensures (\exists integer i; 0 <= i < list1_size && tuple_list_contains(list2, list2_size, list1[i], tuple_size) == 1) <==> (\result == 1);
*/
int find_similar_tuples(int** list1, int list1_size, int** list2, int list2_size, int tuple_size) {
    /*@
      loop invariant 0 <= i <= list1_size;
      // If a similar tuple has been found, result_found is 1.
      loop invariant (result_found == 1) ==> (\exists integer k; 0 <= k < i && tuple_list_contains(list2, list2_size, list1[k], tuple_size) == 1);
      // If no similar tuple has been found yet, result_found is 0.
      loop invariant (result_found == 0) ==> (\forall integer k; 0 <= k < i ==> tuple_list_contains(list2, list2_size, list1[k], tuple_size) == 0);
      loop assigns i, result_found;
      loop variant list1_size - i;
    */
    for (int i = 0; i < list1_size; i++) {
        int result_found = 0; // Rule I.2: Use int for boolean.

        /*@
          loop invariant 0 <= j <= list2_size;
          // If list1[i] is found in list2 up to index j-1.
          loop invariant (result_found == 1) ==> (\exists integer k; 0 <= k < j && tuple_equals(list1[i], list2[k], tuple_size) == 1);
          // If list1[i] is NOT found in list2 up to index j-1.
          loop invariant (result_found == 0) ==> (\forall integer k; 0 <= k < j ==> tuple_equals(list1[i], list2[k], tuple_size) == 0);
          loop assigns j, result_found;
          loop variant list2_size - j;
        */
        for (int j = 0; j < list2_size; j++) {
            int current_tuple_equal = 1; // Assume equal until proven otherwise

            /*@
              loop invariant 0 <= k <= tuple_size;
              // If tuples are unequal, current_tuple_equal is 0.
              loop invariant (current_tuple_equal == 0) ==> (\exists integer l; 0 <= l < k && list1[i][l] != list2[j][l]);
              // If tuples are equal so far, current_tuple_equal is 1.
              loop invariant (current_tuple_equal == 1) ==> (\forall integer l; 0 <= l < k ==> list1[i][l] == list2[j][l]);
              loop assigns k, current_tuple_equal;
              loop variant tuple_size - k;
            */
            for (int k = 0; k < tuple_size; k++) {
                if (list1[i][k] != list2[j][k]) {
                    current_tuple_equal = 0;
                    break;
                }
            }

            if (current_tuple_equal == 1) {
                result_found = 1;
                break;
            }
        }
        if (result_found == 1) {
            return 1;
        }
    }
    return 0;
}
