// Task ID: 2
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Define a tuple structure for logical reasoning.
  // This is a common pattern when dealing with logical properties that mirror C structs or arrays of fixed size.
  axiomatic Tuple {
    logic integer tuple_get_first(int* t);
    logic integer tuple_get_second(int* t);

    axiom tuple_get_first_def{L}(int* t) = \at(t[0], L);
    axiom tuple_get_second_def{L}(int* t) = \at(t[1], L);
  }
*/

/*@
  axiomatic SimilarElements {
    // Recursive logic function to check if a tuple exists in a list.
    // Rule II.1: Recursive logic for complexity.
    logic boolean tuple_in_list(int* t, int (*list)[2], integer count);

    axiom tuple_in_list_base:
      \forall int* t, int (*list)[2];
        tuple_in_list(t, list, 0) == \false;

    axiom tuple_in_list_recursive:
      \forall int* t, int (*list)[2], integer count;
        count > 0 ==>
        tuple_in_list(t, list, count) ==
          ( (tuple_get_first(t) == tuple_get_first(list[count-1]) &&
             tuple_get_second(t) == tuple_get_second(list[count-1])) ||
            tuple_in_list(t, list, count - 1) );

    // Recursive logic function to check if elements are similar in two lists.
    // This is the core logical property we want to verify.
    logic boolean similar_exists(int (*list1)[2], integer count1, int (*list2)[2], integer count2);

    axiom similar_exists_base1:
      \forall int (*list1)[2], int (*list2)[2], integer count2;
        similar_exists(list1, 0, list2, count2) == \false;

    axiom similar_exists_base2:
      \forall int (*list1)[2], int (*list2)[2], integer count1;
        similar_exists(list1, count1, list2, 0) == \false;

    axiom similar_exists_recursive:
      \forall int (*list1)[2], int (*list2)[2], integer count1, integer count2;
        count1 > 0 ==>
        similar_exists(list1, count1, list2, count2) ==
          ( tuple_in_list(list1[count1-1], list2, count2) ||
            similar_exists(list1, count1 - 1, list2, count2) );

    // Rule II.2: Helper axiom to prove that if any elements are similar, the function returns 1.
    // This helps the prover connect the C code's return value to the logical property.
    // This is crucial because the `ensures` clause uses `similar_exists`.
    axiom similar_exists_helper:
      \forall int (*list1)[2], integer count1, int (*list2)[2], integer count2, integer i, integer j;
        0 <= i < count1 && 0 <= j < count2 &&
        tuple_get_first(list1[i]) == tuple_get_first(list2[j]) &&
        tuple_get_second(list1[i]) == tuple_get_second(list2[j]) ==>
        similar_exists(list1, count1, list2, count2) == \true;
  }
*/


/*@
  requires count1 >= 0 && count2 >= 0;
  requires \valid_read_array(list1, count1);
  requires \valid_read_array(list2, count2);

  // Rule II.5: Prevent RTE - Ensure tuple elements are within reasonable bounds if they are used in further calculations.
  // For this problem, int values are fine as long as they fit in int.
  // The problem does not specify constraints on tuple values, so we assume they fit in `int`.

  assigns \nothing;

  // Rule II.3: Ensures clause using logical equivalence.
  // The function returns 1 if and only if there exists at least one similar element.
  ensures (similar_exists(list1, count1, list2, count2)) <==> (\result == 1);
*/
int find_similar_elements(int (*list1)[2], int count1, int (*list2)[2], int count2) {
    /*@
      loop invariant 0 <= i <= count1;
      // If a similar element has already been found, result is 1.
      loop invariant (similar_exists(list1, i, list2, count2)) ==> (\result == 1);
      // If no similar element has been found among the first 'i' elements of list1, result is 0.
      loop invariant (!similar_exists(list1, i, list2, count2)) ==> (\result == 0);
      loop assigns i;
      loop variant count1 - i;
    */
    for (int i = 0; i < count1; i++) {
        /*@
          loop invariant 0 <= j <= count2;
          // If a similar element has been found for list1[i] among the first 'j' elements of list2, result is 1.
          loop invariant (tuple_in_list(list1[i], list2, j)) ==> (\result == 1);
          // If no similar element has been found for list1[i] among the first 'j' elements of list2, result is 0.
          loop invariant (!tuple_in_list(list1[i], list2, j)) ==> (\result == 0);
          loop assigns j;
          loop variant count2 - j;
        */
        for (int j = 0; j < count2; j++) {
            // Accessing elements: list1[i][0] and list1[i][1]
            // Rule I.3: list1 decays to int (*list1)[2], so list1[i] is int[2]
            // Accessing list1[i][0] is correct.
            if (list1[i][0] == list2[j][0] && list1[i][1] == list2[j][1]) {
                return 1; // Found a similar tuple
            }
        }
    }
    return 0; // No similar tuple found
}
