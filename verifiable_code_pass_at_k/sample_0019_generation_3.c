// Task ID: 19
// Generation: 3

/*@
  // Rule II.1, II.2: Define an axiomatic block for recursive logic.
  // This logic function checks if there's a duplicate element in the subarray arr[low..high-1].
  axiomatic HasDuplicate {
    logic boolean has_duplicate_in_range(int *arr, int low, int high);

    // Rule II.2: Base case for the recursive logic.
    axiom has_duplicate_in_range_base:
      \forall int *arr, integer low, high;
        low >= high ==> !has_duplicate_in_range(arr, low, high);

    // Rule II.2: Recursive step for the logic.
    // Checks if the last element arr[high-1] is present in arr[low..high-2]
    // OR if there's a duplicate in arr[low..high-2].
    axiom has_duplicate_in_range_recursive:
      \forall int *arr, integer low, high;
        low < high ==> (
          has_duplicate_in_range(arr, low, high) <==>
          (
            (\exists integer k; low <= k < high - 1 && arr[k] == arr[high - 1]) ||
            has_duplicate_in_range(arr, low, high - 1)
          )
        );

    // Rule II.2, II.1: Helper axiom for the recursive logic.
    // If an element arr[idx] is found in arr[low..idx-1], then there is a duplicate in arr[low..idx].
    axiom has_duplicate_in_range_helper_1:
      \forall int *arr, integer low, idx;
        low <= idx ==> (
          (\exists integer k; low <= k < idx && arr[k] == arr[idx]) ==> has_duplicate_in_range(arr, low, idx + 1)
        );

    // Rule II.2, II.1: Helper axiom for the recursive logic.
    // If there is a duplicate in arr[low..idx], then there is a duplicate in arr[low..idx+1].
    axiom has_duplicate_in_range_helper_2:
      \forall int *arr, integer low, idx;
        low <= idx ==> (
          has_duplicate_in_range(arr, low, idx) ==> has_duplicate_in_range(arr, low, idx + 1)
        );
  }
*/

/*@
  requires N >= 0; // Array size must be non-negative.
  // Rule II.5: Prevent potential out-of-bounds access if N is too large for memory.
  // Although not strictly an overflow, it's a runtime error prevention.
  requires \valid_read(arr + (0..N-1));

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function returns 1 (true) if there exists a duplicate, 0 (false) otherwise.
  ensures (has_duplicate_in_range(arr, 0, N)) <==> (result == 1);
*/
int contains_duplicate(int *arr, int N) { // Rule I.2: Uses int for boolean return.
    /*@
      loop invariant 0 <= i <= N;
      // Rule II.4: Invariant capturing the progress.
      // If a duplicate has been found so far, then found_duplicate is 1.
      loop invariant found_duplicate == 1 ==> has_duplicate_in_range(arr, 0, i);
      // Rule II.4: If no duplicate has been found so far, then found_duplicate is 0.
      loop invariant found_duplicate == 0 ==> !\exists integer k; 0 <= k < i && (\exists integer j; 0 <= j < k && arr[j] == arr[k]);

      // Rule II.4: Loop variant for termination.
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        /*@
          loop invariant 0 <= j <= i;
          // Rule II.4: Inner loop invariant.
          // If a duplicate is found for arr[i], then found_duplicate becomes 1.
          loop invariant found_duplicate == 1 ==> (\exists integer k; 0 <= k < i && arr[k] == arr[i]);
          // Rule II.4: If no duplicate is found for arr[i] yet, then no arr[j] (j<i) equals arr[i].
          loop invariant found_duplicate == 0 ==> !\exists integer k; 0 <= k < j && arr[k] == arr[i];

          // Rule II.4: Inner loop variant for termination.
          loop variant i - j;
        */
        for (int j = 0; j < i; j++) {
            if (arr[i] == arr[j]) {
                return 1; // Rule I.2: Returns 1 for true.
            }
        }
    }
    return 0; // Rule I.2: Returns 0 for false.
}
