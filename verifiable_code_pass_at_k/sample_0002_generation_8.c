// Task ID: 2
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay is handled by ACSL.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory Loop Annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic TupleList {
  // Define a tuple as a pair of integers.
  logic int tuple_first(int* tuple);
  logic int tuple_second(int* tuple);

  axiom tuple_first_def{L}(int* t) = t[0];
  axiom tuple_second_def{L}(int* t) = t[1];

  // Predicate to check if a tuple exists in a list.
  // Rule II.1: Recursive logic for checking existence in a list.
  logic boolean tuple_exists_in_list(int* tuple, int* list, int size, int tuple_size);

  axiom tuple_exists_in_list_base{L}(int* tuple, int* list, int size, int tuple_size) =
    (size == 0) ==> \false;

  axiom tuple_exists_in_list_rec{L}(int* tuple, int* list, int size, int tuple_size) =
    (size > 0) ==>
      ((tuple_first(tuple) == tuple_first(list)) && (tuple_second(tuple) == tuple_second(list))) ||
      tuple_exists_in_list(tuple, list + tuple_size, size - 1, tuple_size);

  // Predicate to check if a tuple from list1 exists in list2.
  logic boolean similar_tuple_exists(int* list1, int size1, int* list2, int size2, int tuple_size);

  axiom similar_tuple_exists_base{L}(int* list1, int size1, int* list2, int size2, int tuple_size) =
    (size1 == 0) ==> \false;

  axiom similar_tuple_exists_rec{L}(int* list1, int size1, int* list2, int size2, int tuple_size) =
    (size1 > 0) ==>
      tuple_exists_in_list(list1, list2, size2, tuple_size) ||
      similar_tuple_exists(list1 + tuple_size, size1 - 1, list2, size2, tuple_size);

  // Helper axiom: if a tuple exists in list1 and list2, it means they are similar elements.
  // Rule II.2: CRITICAL - Helper Axioms.
  axiom similar_elements_implies_exists{L}:
    \forall int* t1, int s1, int* t2, int s2, int ts, int* current_tuple;
      (0 < s1 && 0 < s2 && tuple_exists_in_list(current_tuple, t1, s1, ts) && tuple_exists_in_list(current_tuple, t2, s2, ts)) ==>
      similar_tuple_exists(t1, s1, t2, s2, ts);

  // Helper axiom: if similar_tuple_exists is true, then there exists a tuple in list1 that is also in list2.
  axiom similar_exists_implies_common_tuple{L}:
    \forall int* l1, int s1, int* l2, int s2, int ts;
      similar_tuple_exists(l1, s1, l2, s2, ts) ==>
      \exists int i; 0 <= i < s1 && tuple_exists_in_list(l1 + i * ts, l2, s2, ts);

} */

/*@
  requires size1 >= 0;
  requires size2 >= 0;
  // Rule II.5: Prevent Runtime Errors (RTE) - ensure array access is valid.
  // The arrays should have enough space to hold 'size' tuples, each with 2 elements.
  requires \valid_read(list1 + (size1 * 2) - 1) || size1 == 0;
  requires \valid_read(list2 + (size2 * 2) - 1) || size2 == 0;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (similar_tuple_exists(list1, size1, list2, size2, 2)) <==> (result == 1);
*/
int find_similar_elements(int* list1, int size1, int* list2, int size2) {
    /*@
      loop invariant 0 <= i <= size1;
      // All tuples processed so far from list1 have been checked against list2.
      loop invariant \forall integer k; 0 <= k < i ==>
        (\result == 1 ==> tuple_exists_in_list(list1 + k * 2, list2, size2, 2));
      // If result is 0, no similar tuple has been found among the first 'i' tuples of list1.
      loop invariant (\result == 0) ==>
        (\forall integer k; 0 <= k < i ==> !\exists integer j; 0 <= j < size2 &&
          (list1[k*2] == list2[j*2] && list1[k*2+1] == list2[j*2+1]));

      loop assigns \result; // result is the return value, not a local variable.
      loop variant size1 - i;
    */
    for (int i = 0; i < size1; i++) {
        int current_tuple_first = list1[i * 2];
        int current_tuple_second = list1[i * 2 + 1];

        /*@
          loop invariant 0 <= j <= size2;
          // If a match is found, result will be 1.
          loop invariant (\result == 1) ==>
            (\exists integer k; 0 <= k < j &&
              (current_tuple_first == list2[k*2] && current_tuple_second == list2[k*2+1]));
          // If no match yet, result is still 0.
          loop invariant (\result == 0) ==>
            (\forall integer k; 0 <= k < j ==>
              !(current_tuple_first == list2[k*2] && current_tuple_second == list2[k*2+1]));
          loop assigns \result;
          loop variant size2 - j;
        */
        for (int j = 0; j < size2; j++) {
            if (current_tuple_first == list2[j * 2] && current_tuple_second == list2[j * 2 + 1]) {
                return 1; // Found a similar tuple
            }
        }
    }
    return 0; // No similar tuple found after checking all elements
}
