// Task ID: 46
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define a recursive logic function to check for distinctness.
  // This approach avoids complex quantifiers directly in ensures clauses
  // and allows for helper axioms.
  axiomatic Distinctness {
    logic int are_elements_distinct{L}(int *arr, int len);

    // Base case: An empty array or an array with one element has distinct elements.
    axiom distinct_base_empty:
      \forall int *arr, int len;
        len <= 1 ==> are_elements_distinct(arr, len) == 1;

    // Recursive step: Elements are distinct if the first (len-1) elements are distinct
    // AND the last element is not equal to any of the first (len-1) elements.
    axiom distinct_recursive:
      \forall int *arr, int len;
        len > 1 ==> (
          are_elements_distinct(arr, len) == (
            are_elements_distinct(arr, len - 1) == 1 &&
            (\forall integer i; 0 <= i < len - 1 ==> arr[i] != arr[len - 1])
          )
        );

    // Rule II.2: Helper axiom to prove if all elements are distinct, then no two elements are equal.
    // This helps the prover connect the recursive definition to the common understanding of distinctness.
    axiom distinct_helper_no_equality:
      \forall int *arr, int len;
        are_elements_distinct(arr, len) == 1 ==>
        (\forall integer i, j; 0 <= i < len && 0 <= j < len && i != j ==> arr[i] != arr[j]);

    // Helper axiom to prove if there exist two equal elements, then they are not distinct.
    axiom distinct_helper_equality_implies_not_distinct:
      \forall int *arr, int len;
        (\exists integer i, j; 0 <= i < len && 0 <= j < len && i != j && arr[i] == arr[j]) ==>
        are_elements_distinct(arr, len) == 0;
  }
*/

/*@
  requires len >= 0;
  // Rule II.5: Prevent RTE for array access if len > 0.
  requires len == 0 || \valid_read_range(arr, 0, len - 1);

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The result is 1 (true) if and only if all elements in the array are distinct.
  ensures (are_elements_distinct(arr, len) == 1) <==> (esult == 1);
*/
int are_all_elements_distinct(int *arr, int len) {
    // Rule II.5: Handle edge cases for empty or single-element arrays.
    // These are covered by the axiomatic definition's base case.
    if (len <= 1) {
        return 1; // All elements are distinct (vacuously true for len 0 or 1).
    }

    /*@
      loop invariant 0 <= i <= len;
      // All elements from arr[0] to arr[i-1] are distinct among themselves.
      loop invariant are_elements_distinct(arr, i) == 1;
      // No element from arr[0] to arr[i-1] is equal to arr[j] for j >= i.
      // This invariant is crucial for proving the distinctness property.
      loop invariant \forall integer k; 0 <= k < i ==> (\forall integer m; i <= m < len ==> arr[k] != arr[m]);

      loop assigns i, j; // The loop only modifies i and j, not the array elements themselves.

      // Rule II.4: Loop variant for termination.
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        /*@
          loop invariant i + 1 <= j <= len;
          // arr[i] is not equal to any element arr[k] where i+1 <= k < j.
          loop invariant \forall integer k; i + 1 <= k < j ==> arr[i] != arr[k];

          loop assigns j;

          // Rule II.4: Loop variant for termination.
          loop variant len - j;
        */
        for (int j = i + 1; j < len; j++) {
            if (arr[i] == arr[j]) {
                return 0; // Found a duplicate.
            }
        }
    }

    return 1; // No duplicates found.
}
