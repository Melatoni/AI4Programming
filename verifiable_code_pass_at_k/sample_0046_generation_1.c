// Task ID: 46
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for Booleans.
  // Rule I.3: Array pointer decay handled for parameter type.

  // Rule II.5: Preconditions to prevent runtime errors (e.g., array out of bounds).
  requires n >= 0;
  requires n <= 100000; // Limit n to prevent excessive loop iterations or memory use for large arrays.
  
  // Rule II.2: Helper axioms are not directly needed for this problem as there are no complex recursive logic functions.
  // Rule II.3: Ensures clause for boolean-like function.
  // Rule II.4: Mandatory loop annotations.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (\exists integer i, j; 0 <= i < j < n && a[i] == a[j]) <==> (esult == 0);
  // If all elements are different, then no such i, j exist, and the result is 1.
  // If there exist i, j such that a[i] == a[j], then the result is 0.
*/
int are_all_different(int* a, int n) {
    /*@
      loop invariant 0 <= i <= n;
      // Invariant: For all elements processed so far (from 0 to i-1),
      // they are all distinct from each other.
      loop invariant \forall integer k, l; 0 <= k < l < i ==> a[k] != a[l];
      loop assigns i, j; // i and j are loop variables.
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i < j <= n;
          // Invariant: All elements from a[i] up to a[j-1] are distinct from a[i].
          loop invariant \forall integer k; i < k < j ==> a[i] != a[k];
          loop assigns j; // j is a loop variable.
          loop variant n - j;
        */
        for (int j = i + 1; j < n; j++) {
            // Rule II.5: Array access a[i] and a[j] are guarded by loop conditions i < n and j < n.
            if (a[i] == a[j]) {
                return 0; // Found a duplicate, so not all are different.
            }
        }
    }
    return 1; // No duplicates found after checking all pairs.
}
