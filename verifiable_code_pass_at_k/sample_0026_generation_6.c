// Task ID: 26
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay `int (*tuple_list)[2]`.

  // Rule II.1, II.2: Recursive logic for complexity.
  axiomatic AllKElements {
    logic boolean has_k_element(int k, int* arr, int start, int end);

    axiom has_k_element_base:
      \forall int k, int* arr, int start, int end;
        start > end ==> !has_k_element(k, arr, start, end);

    axiom has_k_element_recursive:
      \forall int k, int* arr, int start, int end;
        start <= end ==> (has_k_element(k, arr, start, end) <==>
                          (arr[start] == k || has_k_element(k, arr, start + 1, end)));
  }
*/

/*@
  requires n >= 0;
  requires k >= 0; // Assuming k is a non-negative element value
  requires \valid_read(tuple_list + (0..n-1)); // Ensure tuple_list is readable up to n elements.
  // Rule II.5: Prevent runtime errors.
  // This function doesn't involve arithmetic operations that typically overflow,
  // but we ensure array access is within bounds.

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like function uses logical equivalence.
  ensures (\forall integer i; 0 <= i < n ==> has_k_element(k, tuple_list[i], 0, 1)) <==> (\result == 1);
*/
int check_all_k_elements(int (*tuple_list)[2], int n, int k) {
    /*@
      loop invariant 0 <= i <= n;
      // Rule II.4: Loop invariant capturing the state.
      loop invariant \forall integer j; 0 <= j < i ==> (tuple_list[j][0] == k || tuple_list[j][1] == k);
      loop assigns i;
      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // Rule I.2: Representing boolean logic with int.
        // Rule III.1: No C-style ternary in ACSL.
        // Rule III.2: No parentheses around if-then-else.
        // Rule III.3: Correct range syntax.
        // Rule III.4: No stray semicolons.
        if (!((tuple_list[i][0] == k) || (tuple_list[i][1] == k))) {
            return 0; // If any tuple does not contain k, return false.
        }
    }
    return 1; // All tuples contain k.
}
