// Task ID: 26
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here.

  // Rule II.1: Recursive logic for complexity - not applicable here.
  // Rule II.2: Helper axioms - not applicable here.
  // Rule II.3: Ensures clause for boolean-like functions.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.

  requires 0 <= num_tuples;
  requires 0 <= k;
  requires \valid_read(tuples + (0..num_tuples - 1));

  assigns \nothing;

  // Define a logic function to check if a specific element 'e' exists in the tuple list.
  // This is a helper for the main ensures clause.
  logic boolean element_exists_in_tuples(int e, int* tuples, int num_tuples) =
    \exists integer i; 0 <= i < num_tuples && tuples[i] == e;

  // The main ensures clause:
  // The function returns 1 if and only if all integers from 0 to k-1 exist in the tuples array.
  ensures (\forall integer e; 0 <= e < k ==> element_exists_in_tuples(e, tuples, num_tuples)) <==> (\result == 1);
*/
int has_all_k_elements(int* tuples, int num_tuples, int k) {
    /*@
      loop invariant 0 <= i && i <= k;
      // Invariant: All elements from 0 to i-1 have been found so far.
      loop invariant \forall integer e; 0 <= e < i ==> (\exists integer j; 0 <= j < num_tuples && tuples[j] == e);
      loop assigns i;
      loop variant k - i;
    */
    for (int i = 0; i < k; ++i) {
        int found_current_element = 0; // Rule I.2: Use int for boolean.

        /*@
          loop invariant 0 <= j && j <= num_tuples;
          // Invariant: If 'found_current_element' is 1, then tuples[l] == i for some l < j.
          // If 'found_current_element' is 0, then tuples[l] != i for all l < j.
          loop invariant (found_current_element == 1) ==> (\exists integer l; 0 <= l < j && tuples[l] == i);
          loop invariant (found_current_element == 0) ==> (\forall integer l; 0 <= l < j ==> tuples[l] != i);
          loop assigns j, found_current_element;
          loop variant num_tuples - j;
        */
        for (int j = 0; j < num_tuples; ++j) {
            if (tuples[j] == i) {
                found_current_element = 1;
                // Once found, we can break the inner loop.
                // Frama-C/WP can often infer the loop invariant after a break,
                // but a 'break' statement might require more manual assistance
                // in complex scenarios. For this simple case, it's fine.
                break;
            }
        }

        if (found_current_element == 0) {
            // If the current element 'i' was not found in the entire list,
            // then not all k elements are present.
            return 0;
        }
    }

    // If the loop completes, it means all elements from 0 to k-1 were found.
    return 1;
}
