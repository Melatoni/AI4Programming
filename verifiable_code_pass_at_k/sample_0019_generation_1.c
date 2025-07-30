// Task ID: 19
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  axiomatic HasDuplicate {
    logic boolean has_duplicate_in_range(int *a, int low, int high);

    axiom has_duplicate_base:
      \forall int *a, int low;
        has_duplicate_in_range(a, low, low) == \false;

    axiom has_duplicate_recursive:
      \forall int *a, int low, int high;
        low < high ==>
        has_duplicate_in_range(a, low, high) ==
        (has_duplicate_in_range(a, low, high - 1) ||
         (\exists integer k; low <= k < high && a[k] == a[high]));
  }
*/

/*@
  requires N >= 0;
  // Rule II.5: Prevent runtime errors. Array access requires valid range.
  requires \valid_read_range(a, 0, N - 1);

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence.
  ensures has_duplicate_in_range(a, 0, N - 1) <==> ( \result == 1 );
*/
int contains_duplicate(int *a, int N) {
    /*@
      loop invariant 0 <= i <= N;
      // Rule II.4: Loop invariants are mandatory.
      // The outer loop invariant asserts that no duplicates have been found so far
      // between elements a[0]...a[i-1].
      loop invariant \forall integer x, y; 0 <= x < y < i ==> a[x] != a[y];
      loop assigns i, j;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        /*@
          loop invariant i < j <= N;
          // Inner loop invariant: No duplicate found between a[i] and a[i+1]...a[j-1].
          loop invariant \forall integer k; i < k < j ==> a[i] != a[k];
          loop assigns j;
          loop variant N - j;
        */
        for (int j = i + 1; j < N; j++) {
            if (a[i] == a[j]) {
                return 1; // Found a duplicate
            }
        }
    }
    return 0; // No duplicate found
}
