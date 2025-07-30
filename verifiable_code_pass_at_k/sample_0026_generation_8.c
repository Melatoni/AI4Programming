// Task ID: 26
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for Booleans.
  // Rule I.3: Array pointer decay - not applicable here as it's a 1D array.

  // Rule II.1: No \sum. Recursive logic not needed for this problem.
  // Rule II.2: Helper axioms not needed for this problem.

  // Rule II.5: Prevent Runtime Errors (RTE).
  // The 'elements' array contains integers, and 'k' is also an integer.
  // The size of the array 'n' must be non-negative.
  requires n >= 0;
  // 'k' must be non-negative, as it represents a count of elements.
  requires k >= 0;
  // Each element in 'elements' must be non-negative.
  // If elements could be negative, the logic for 'found' would need adjustment.
  requires \forall integer i; 0 <= i < n ==> elements[i] >= 0;

  // No memory allocation or modification.
  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  // The function returns 1 if all integers from 0 to k-1 are present in 'elements'.
  // It returns 0 otherwise.
  ensures (\forall integer val; 0 <= val < k ==> (\exists integer i; 0 <= i < n && elements[i] == val)) <==> (result == 1);
*/
int has_all_k_elements(int elements[], int n, int k) {
    /*@
      loop invariant 0 <= i && i <= k;
      // All values from 0 to i-1 have been found so far.
      loop invariant \forall integer val; 0 <= val < i ==> (\exists integer j; 0 <= j < n && elements[j] == val);
      loop assigns i;
      // Rule II.4: Loop variant for termination.
      loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        int found = 0; // Rule I.2: Use int for boolean.
        /*@
          loop invariant 0 <= j && j <= n;
          // If 'found' is 1, then the current value 'i' has been found at some index < j.
          loop invariant (found == 1) ==> (\exists integer l; 0 <= l < j && elements[l] == i);
          // If 'found' is 0, then the current value 'i' has not been found in elements[0..j-1].
          loop invariant (found == 0) ==> (\forall integer l; 0 <= l < j ==> elements[l] != i);
          loop assigns j, found; // 'found' is assigned within the loop.
          // Rule II.4: Loop variant for termination.
          loop variant n - j;
        */
        for (int j = 0; j < n; j++) {
            if (elements[j] == i) {
                found = 1;
                // Once found, no need to check further for this 'i'.
                break;
            }
        }
        // If 'i' was not found in the entire 'elements' array, then not all k elements are present.
        // Rule III.1: No C-style ternary in ACSL.
        // Rule III.2: No parentheses around if-then-else.
        // Rule III.3: Correct range syntax.
        // Rule III.4: No stray semicolons.
        if (found == 0) {
            return 0; // Corresponds to the 'false' case of the outer ensures clause.
        }
    }
    // If the loop completes, it means all values from 0 to k-1 were found.
    return 1; // Corresponds to the 'true' case of the outer ensures clause.
}
