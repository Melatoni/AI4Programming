// Task ID: 19
// Generation: 7

/*@
  // Rule II.1: Define a recursive logic function to check for duplicates in a subarray.
  axiomatic Duplicates {
    logic boolean has_duplicate_in_subarray(int* arr, int start, int end)
      reads arr[start..end];

    // Base case: An empty or single-element subarray has no duplicates.
    axiom has_duplicate_in_subarray_base1:
      \forall int* arr, int start, int end;
      start >= end ==> !has_duplicate_in_subarray(arr, start, end);

    // Recursive case: Check if the last element is duplicated in the previous part,
    // or if the previous part itself has duplicates.
    axiom has_duplicate_in_subarray_recursive:
      \forall int* arr, int start, int end;
      start < end ==>
      (has_duplicate_in_subarray(arr, start, end) <==>
       (\exists integer k; start <= k < end && arr[k] == arr[end]) ||
       has_duplicate_in_subarray(arr, start, end - 1));

    // Rule II.2: Helper axiom to prove if a subarray has no duplicates,
    // then adding a new unique element doesn't create duplicates.
    // This helps the prover with the loop invariant.
    axiom has_duplicate_in_subarray_helper_no_dup:
      \forall int* arr, int start, int end, int val;
      !has_duplicate_in_subarray(arr, start, end) &&
      (\forall integer k; start <= k <= end && arr[k] != val) ==>
      !has_duplicate_in_subarray(arr, start, end + 1) && arr[end+1] == val;

    // Helper axiom for the case where a duplicate is found
    axiom has_duplicate_in_subarray_helper_found_dup:
      \forall int* arr, int start, int end, int val;
      !has_duplicate_in_subarray(arr, start, end) &&
      (\exists integer k; start <= k <= end && arr[k] == val) ==>
      has_duplicate_in_subarray(arr, start, end + 1) && arr[end+1] == val;
  }
*/

/*@
  requires n >= 0;
  requires \valid_read_range(arr, 0, n - 1);
  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return.
  ensures (\exists integer i, j; 0 <= i < j < n && arr[i] == arr[j]) <==> (esult == 1);
  // Alternative equivalent ensures clause using the axiomatic definition:
  // ensures has_duplicate_in_subarray(arr, 0, n - 1) <==> (esult == 1);
*/
int contains_duplicate(int* arr, int n) { // Rule I.2: Uses int for boolean.
    /*@
      loop invariant 0 <= i <= n;
      // The outer loop invariant states that no duplicates have been found in the prefix arr[0..i-1]
      // and that the subarray arr[0..i-1] does not contain duplicates within itself.
      loop invariant \forall integer k; 0 <= k < i ==>
        (\forall integer l; 0 <= l < k ==> arr[k] != arr[l]);
      // This is equivalent to: !has_duplicate_in_subarray(arr, 0, i - 1);

      loop assigns i, j;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i < j <= n;
          // The inner loop invariant states that arr[i] has not been found
          // in arr[i+1..j-1].
          loop invariant \forall integer k; i < k < j ==> arr[i] != arr[k];
          loop assigns j;
          loop variant n - j;
        */
        for (int j = i + 1; j < n; j++) {
            if (arr[i] == arr[j]) {
                return 1; // Duplicate found
            }
        }
    }
    return 0; // No duplicate found
}
