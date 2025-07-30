// Task ID: 26
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here.

  // Rule II.1: Recursive logic for complexity - not directly applicable for this problem,
  // but if we were to define "all k elements" as a property over a sequence,
  // we might use a recursive logic function.

  // Rule II.5: Prevent Runtime Errors (RTE)
  // Ensure array indices are within bounds.
  // k should be non-negative.
  // The number of tuples (n) should be non-negative.
  requires k >= 0;
  requires n >= 0;
  requires \valid_read(tuples + (0..n-1)); // Ensure the array is readable.
  requires \forall integer i; 0 <= i < n ==> \valid_read(tuples[i] + (0..1)); // Ensure each tuple is readable.

  // Rule II.3: ensures clause for Boolean-like functions using <==>.
  // The function returns 1 if all k elements from 0 to k-1 are present in the 'tuples' array.
  // It returns 0 otherwise.
  ensures (\forall integer val; 0 <= val < k ==> (\exists integer i; 0 <= i < n && (tuples[i][0] == val || tuples[i][1] == val))) <==> (\result == 1);
*/
int has_all_k_elements(int* tuples[], int n, int k) {
    /*@
      // Rule I.2: Use int for booleans.
      // Rule II.1: Recursive logic for complexity - not directly applicable.
      // Rule II.2: Helper Axioms - not directly applicable for this simple check.
      // Rule II.5: Prevent Runtime Errors (RTE) - check for k=0 early.
    */
    if (k == 0) {
        return 1; // If k is 0, then all 0 elements are "present".
    }

    /*@
      // Rule II.4: Mandatory Loop Annotations.
      // Outer loop: iterates through each required value from 0 to k-1.
      loop invariant 0 <= i <= k;
      // All values from 0 to i-1 have been found.
      loop invariant \forall integer val; 0 <= val < i ==> (\exists integer idx; 0 <= idx < n && (tuples[idx][0] == val || tuples[idx][1] == val));
      loop assigns i, has_found_current_val;
      loop variant k - i;
    */
    for (int i = 0; i < k; ++i) {
        int has_found_current_val = 0; // Rule I.2: Use int for booleans.

        /*@
          // Rule II.4: Mandatory Loop Annotations.
          // Inner loop: searches for the current value 'i' in the 'tuples' array.
          loop invariant 0 <= j <= n;
          // The current value 'i' has not been found in tuples[0]...tuples[j-1]
          // if has_found_current_val is still 0.
          loop invariant (has_found_current_val == 0) ==> (\forall integer idx; 0 <= idx < j ==> (tuples[idx][0] != i && tuples[idx][1] != i));
          // If has_found_current_val is 1, then 'i' has been found in tuples[0]...tuples[j-1].
          loop invariant (has_found_current_val == 1) ==> (\exists integer idx; 0 <= idx < j && (tuples[idx][0] == i || tuples[idx][1] == i));
          loop assigns j, has_found_current_val;
          loop variant n - j;
        */
        for (int j = 0; j < n; ++j) {
            // Rule II.5: Prevent Runtime Errors (RTE) - array access within bounds.
            // This is ensured by the requires clause: \valid_read(tuples[j] + (0..1))
            if (tuples[j][0] == i || tuples[j][1] == i) {
                has_found_current_val = 1;
                break;
            }
        }

        if (has_found_current_val == 0) {
            return 0; // If any required value is not found, return 0.
        }
    }

    return 1; // All k elements were found.
}
