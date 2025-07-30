// Task ID: 19
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in formal parameters.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms are CRITICAL.
  // Rule II.3: ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Axiomatic block for recursive logic to define "has_duplicate" property.
  // This avoids using quantifiers over ranges directly in ensures clauses,
  // making it easier for WP to prove.
  axiomatic HasDuplicate {
    logic boolean has_duplicate{L}(int* a, int n);

    // Base case: An array with 0 or 1 element cannot have duplicates.
    axiom has_duplicate_base_0{L}:
      \forall int* a, int n; n <= 1 ==> !has_duplicate(a, n);

    // Recursive case: An array has duplicates if the first element is found
    // in the rest of the array, OR if the rest of the array (excluding the first)
    // has duplicates.
    axiom has_duplicate_rec{L}:
      \forall int* a, int n; n > 1 ==>
        (has_duplicate(a, n) <==>
         (\exists integer k; 1 <= k < n && a[0] == a[k]) || has_duplicate(a + 1, n - 1));

    // Helper axiom: If an element is found at index i, and another at index j,
    // where i != j, then there's a duplicate. This helps WP connect the loop logic
    // to the overall property.
    axiom has_duplicate_helper{L}:
      \forall int* a, int n;
        (\exists integer i, j; 0 <= i < n && 0 <= j < n && i != j && a[i] == a[j]) <==>
        has_duplicate(a, n);
  }
*/

/*@
  // The function finds if an array contains any duplicate element.
  // @param arr: The array of integers.
  // @param n: The number of elements in the array.
  // @return: 1 if duplicates are found, 0 otherwise.

  requires n >= 0;
  requires \valid_read_array(arr, n); // Ensure the array is readable.

  assigns \nothing; // The function does not modify the array.

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // It connects the function's return value to the axiomatic definition of has_duplicate.
  ensures has_duplicate(arr, n) <==> (\result == 1);
*/
int contains_duplicate(int* arr, int n) {
    /*@
      loop invariant 0 <= i <= n;
      // Invariant: No duplicates have been found in the subarray arr[0..i-1].
      // This is expressed in terms of the axiomatic property.
      loop invariant !\exists integer k, l; 0 <= k < i && 0 <= l < i && k != l && arr[k] == arr[l];

      loop assigns i, j; // The loop modifies i and j.
      loop variant n - i; // Variant for the outer loop.
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i + 1 <= j <= n;
          // Invariant: arr[i] has not been found in arr[i+1..j-1].
          loop invariant !\exists integer k; i + 1 <= k < j && arr[i] == arr[k];

          loop assigns j; // The inner loop modifies j.
          loop variant n - j; // Variant for the inner loop.
        */
        for (int j = i + 1; j < n; j++) {
            if (arr[i] == arr[j]) {
                return 1; // Duplicate found.
            }
        }
    }
    return 0; // No duplicates found after checking all pairs.
}
