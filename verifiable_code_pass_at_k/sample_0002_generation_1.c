// Task ID: 2
// Generation: 1

/*@
  // Rule I.2: Represent boolean logic using int.
  // Rule I.1: No standard libraries.
  // Rule I.3: Array pointer decay - T (*arr)[C]
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms.
  // Rule II.3: CRITICAL - ensures clause for Boolean-like functions.
  // Rule II.4: Mandatory Loop Annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic TupleList {
  logic integer tuple_size;
  logic integer tuple_get_first(int* tuple);
  logic integer tuple_get_second(int* tuple);

  axiom tuple_size_axiom: tuple_size == 2;

  // Helper axiom: For a valid tuple, its elements are within integer bounds.
  // This is a minimal example; more specific bounds might be needed depending on context.
  axiom tuple_element_bounds:
    \forall int* tuple;
      \valid(tuple) && \valid(tuple + 1) ==>
      (INT_MIN <= tuple_get_first(tuple) <= INT_MAX &&
       INT_MIN <= tuple_get_second(tuple) <= INT_MAX);

  // Define properties for a tuple list (array of tuples)
  // A tuple list is an array of int, where every two consecutive elements form a tuple.
  // list is int* list, size is the number of int elements, so actual tuples_count = size / 2.

  logic boolean tuple_list_contains_tuple(int* list, int size, int* target_tuple) =
    size >= 2 && size % 2 == 0 &&
    (\exists integer i;
      0 <= i < size / 2 &&
      tuple_get_first(list + i * 2) == tuple_get_first(target_tuple) &&
      tuple_get_second(list + i * 2) == tuple_get_second(target_tuple));

  // Helper axiom: If a tuple list contains a tuple, its size must be at least 2 and even.
  axiom tuple_list_contains_tuple_size:
    \forall int* list, int size, int* target_tuple;
      tuple_list_contains_tuple(list, size, target_tuple) ==> (size >= 2 && size % 2 == 0);

  // Helper axiom: If a tuple list contains a tuple, the target tuple is valid.
  axiom tuple_list_contains_tuple_target_valid:
    \forall int* list, int size, int* target_tuple;
      tuple_list_contains_tuple(list, size, target_tuple) ==> \valid(target_tuple) && \valid(target_tuple + 1);

  // Helper axiom: The tuple list itself must be valid for the function to hold.
  axiom tuple_list_contains_tuple_list_valid:
    \forall int* list, int size, int* target_tuple;
      tuple_list_contains_tuple(list, size, target_tuple) ==> \valid_read(list + (0..(size - 1)));

} */

/*@ axiomatic SimilarTuples {
  // Recursive logic function to count similar elements.
  // list1_ptr and list2_ptr are int*, representing the start of the arrays.
  // size1 and size2 are the total number of int elements in each list.
  // The actual number of tuples is sizeX / 2.

  logic integer count_similar_tuples_recursive(int* list1_ptr, int size1, int* list2_ptr, int size2, integer current_index);

  // Base case: If current_index reaches the end of list1, no more tuples to check.
  axiom count_similar_tuples_base:
    \forall int* list1_ptr, int size1, int* list2_ptr, int size2, integer current_index;
      current_index >= size1 / 2 ==> count_similar_tuples_recursive(list1_ptr, size1, list2_ptr, size2, current_index) == 0;

  // Recursive case: Check the current tuple and recurse.
  axiom count_similar_tuples_recursive_step:
    \forall int* list1_ptr, int size1, int* list2_ptr, int size2, integer current_index;
      0 <= current_index < size1 / 2 && size1 % 2 == 0 && size2 % 2 == 0 &&
      \valid_read(list1_ptr + current_index * 2) && \valid_read(list1_ptr + current_index * 2 + 1) &&
      \valid_read(list2_ptr + (0..(size2 - 1))) ==>
      count_similar_tuples_recursive(list1_ptr, size1, list2_ptr, size2, current_index) ==
      (if tuple_list_contains_tuple(list2_ptr, size2, list1_ptr + current_index * 2)
       then 1
       else 0) + count_similar_tuples_recursive(list1_ptr, size1, list2_ptr, size2, current_index + 1);

  // Helper axiom: The total count of similar tuples is the recursive count starting from index 0.
  logic integer total_similar_tuples(int* list1_ptr, int size1, int* list2_ptr, int size2) =
    count_similar_tuples_recursive(list1_ptr, size1, list2_ptr, size2, 0);

  // Helper axiom: The total similar tuples is non-negative.
  axiom total_similar_tuples_non_negative:
    \forall int* list1_ptr, int size1, int* list2_ptr, int size2;
      total_similar_tuples(list1_ptr, size1, list2_ptr, size2) >= 0;

  // Helper axiom: The total similar tuples is at most the number of tuples in list1.
  axiom total_similar_tuples_upper_bound:
    \forall int* list1_ptr, int size1, int* list2_ptr, int size2;
      total_similar_tuples(list1_ptr, size1, list2_ptr, size2) <= size1 / 2;

} */

/*@
  requires size1 >= 0 && size1 % 2 == 0;
  requires size2 >= 0 && size2 % 2 == 0;

  // Prevent invalid memory access for empty lists
  requires size1 == 0 ==> list1 == \null;
  requires size2 == 0 ==> list2 == \null;

  // Ensure validity of the input arrays for read access if they are not empty.
  requires size1 > 0 ==> \valid_read(list1 + (0..(size1 - 1)));
  requires size2 > 0 ==> \valid_read(list2 + (0..(size2 - 1)));

  assigns \nothing;

  ensures \result == total_similar_tuples(list1, size1, list2, size2);
  ensures \result >= 0;
  ensures \result <= size1 / 2;
*/
int find_similar_tuples(int* list1, int size1, int* list2, int size2) {
    int similar_count = 0;

    /*@
      loop invariant 0 <= i <= size1 / 2;
      loop invariant similar_count == count_similar_tuples_recursive(list1, size1, list2, size2, 0) - count_similar_tuples_recursive(list1, size1, list2, size2, i);
      // The invariant above can also be written as a sum for clarity, but the recursive logic is preferred for proof:
      // \forall integer k; 0 <= k < i ==>
      //   (tuple_list_contains_tuple(list2, size2, list1 + k * 2) ==>
      //    \at(similar_count, LoopEntry) + (\numof(j, 0 <= j < i && tuple_list_contains_tuple(list2, size2, list1 + j * 2))) == similar_count);
      // This is effectively saying similar_count accumulates correctly.

      loop assigns similar_count, i;
      loop variant size1 / 2 - i;
    */
    for (int i = 0; i < size1 / 2; i++) {
        // Current tuple from list1 is (list1[i*2], list1[i*2 + 1])
        // Check if this tuple exists in list2
        /*@
          loop invariant 0 <= j <= size2 / 2;
          loop invariant \forall integer k; 0 <= k < j ==>
            !(tuple_get_first(list1 + i * 2) == tuple_get_first(list2 + k * 2) &&
              tuple_get_second(list1 + i * 2) == tuple_get_second(list2 + k * 2));
          loop invariant (found_match == 1) ==>
            (\exists integer k; 0 <= k < j &&
              tuple_get_first(list1 + i * 2) == tuple_get_first(list2 + k * 2) &&
              tuple_get_second(list1 + i * 2) == tuple_get_second(list2 + k * 2));
          loop invariant (found_match == 0) ==>
            (\forall integer k; 0 <= k < j ==>
              !(tuple_get_first(list1 + i * 2) == tuple_get_first(list2 + k * 2) &&
                tuple_get_second(list1 + i * 2) == tuple_get_second(list2 + k * 2)));

          loop assigns j, found_match;
          loop variant size2 / 2 - j;
        */
        int found_match = 0; // Rule I.2: Use int for boolean
        for (int j = 0; j < size2 / 2; j++) {
            if (list1[i * 2] == list2[j * 2] && list1[i * 2 + 1] == list2[j * 2 + 1]) {
                found_match = 1;
                break; // Found a match, no need to check further in list2
            }
        }
        if (found_match == 1) {
            similar_count++;
        }
    }

    return similar_count;
}
