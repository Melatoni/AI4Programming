// Task ID: 19
// Generation: 2

/*@
  // Rule II.2: Define recursive logic for checking duplicates within a range.
  axiomatic HasDuplicate {
    logic boolean has_duplicate_in_range(int *arr, int start, int end);

    // Base case: An empty or single-element range cannot have duplicates.
    axiom has_duplicate_in_range_base:
      \forall int *arr, int start, int end;
        start >= end ==> !has_duplicate_in_range(arr, start, end);

    // Recursive case: Check if arr[end-1] is present in arr[start..end-2]
    // OR if there's a duplicate in arr[start..end-2].
    axiom has_duplicate_in_range_rec:
      \forall int *arr, int start, int end;
        start < end ==>
        (has_duplicate_in_range(arr, start, end) <==>
         (\exists integer k; start <= k < end - 1 && arr[k] == arr[end-1]) ||
         has_duplicate_in_range(arr, start, end - 1));

    // Rule II.2, II.1: Helper axiom for a specific property.
    // If a duplicate exists in arr[start..end], then there exist two distinct indices
    // i and j within that range such that arr[i] == arr[j].
    axiom has_duplicate_implies_indices:
      \forall int *arr, int start, int end;
        has_duplicate_in_range(arr, start, end) ==>
        (\exists integer i, j; start <= i < j < end && arr[i] == arr[j]);

    // Helper axiom for the reverse direction.
    // If two distinct indices have the same value, then a duplicate exists.
    axiom indices_implies_has_duplicate:
      \forall int *arr, int start, int end;
        (\exists integer i, j; start <= i < j < end && arr[i] == arr[j]) ==>
        has_duplicate_in_range(arr, start, end);
  }
*/

/*@
  requires n >= 0;
  requires \valid_read_range(arr, 0, n - 1); // Ensure array is readable.

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The function returns 1 (true) if there exists a duplicate in the array,
  // 0 (false) otherwise.
  ensures (has_duplicate_in_range(arr, 0, n) <==> \result == 1);
*/
int contains_duplicate(int *arr, int n) { // Rule I.1: No standard libraries. Rule I.2: int for boolean.
    /*@
      loop invariant 0 <= i <= n;
      // All elements in arr[0..i-1] are distinct.
      loop invariant !has_duplicate_in_range(arr, 0, i);
      loop assigns i;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i + 1 <= j <= n;
          // All elements in arr[i+1..j-1] are distinct from arr[i].
          loop invariant \forall integer k; i + 1 <= k < j ==> arr[k] != arr[i];
          loop assigns j;
          loop variant n - j;
        */
        for (int j = i + 1; j < n; j++) {
            if (arr[i] == arr[j]) {
                return 1; // Duplicate found.
            }
        }
    }
    return 0; // No duplicate found after checking all pairs.
}
