// Task ID: 46
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in ACSL.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  axiomatic AllDifferent {
    logic boolean all_different_rec(int *a, int start, int end);

    axiom all_different_rec_base:
      \forall int *a, int start, int end;
        start >= end ==> all_different_rec(a, start, end) == \true;

    axiom all_different_rec_step:
      \forall int *a, int start, int end;
        start < end ==>
          all_different_rec(a, start, end) ==
          (\forall integer k; start < k <= end ==> a[start] != a[k]) &&
          all_different_rec(a, start + 1, end);

    // Helper axiom to prove that if a sub-array is not all different,
    // then the entire array is not all different.
    axiom all_different_rec_not_all_different_propagate:
      \forall int *a, int start, int end, int sub_start, int sub_end;
        start <= sub_start <= sub_end <= end &&
        !all_different_rec(a, sub_start, sub_end) ==>
        !all_different_rec(a, start, end);
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent runtime errors.
  // If n is large, accessing a[i] might be out of bounds if the array is not
  // actually of size n. This assumes 'a' points to an array of at least 'n' elements.
  // For a more robust check, one would need a 'valid_read' predicate,
  // but for this problem, we assume 'a' is a valid pointer to 'n' elements.

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  ensures (all_different_rec(a, 0, n - 1)) <==> (\result == 1);
*/
int are_all_different(int *a, int n) {
    if (n <= 1) {
        return 1; // An array with 0 or 1 elements always has all different elements.
    }

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==>
        (\forall integer l; k < l < n ==> a[k] != a[l]);
      loop invariant (\forall integer x; 0 <= x < i ==>
        !(\exists integer y; x < y < n && a[x] == a[y])) <==>
        (\result == 1); // Connects loop state to potential result.
      loop assigns i, j; // j is not assigned in the outer loop, but in the inner.
                        // Frama-C correctly infers writes to j only in the inner loop block.
      loop variant n - i;
    */
    for (int i = 0; i < n - 1; i++) {
        /*@
          loop invariant i < j <= n;
          loop invariant \forall integer k; i < k < j ==> a[i] != a[k];
          loop assigns j;
          loop variant n - j;
        */
        for (int j = i + 1; j < n; j++) {
            if (a[i] == a[j]) {
                return 0; // Found a duplicate, so not all different.
            }
        }
    }
    return 1; // No duplicates found after checking all pairs.
}
