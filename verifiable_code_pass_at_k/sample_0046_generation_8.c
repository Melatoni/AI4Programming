// Task ID: 46
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define a recursive logic function for uniqueness.
  // This axiomatic block defines what it means for elements in a subarray to be distinct.
  axiomatic UniqueArray {
    logic boolean are_elements_unique{L}(int *arr, int start, int end);

    // If the subarray is empty or contains one element, they are unique.
    axiom unique_base_case{L}:
      \forall int *arr, int start, int end;
        start >= end ==> are_elements_unique(arr, start, end) == \true;

    // To be unique, the last element must not be present in the preceding subarray,
    // and the preceding subarray must itself be unique.
    axiom unique_recursive_case{L}:
      \forall int *arr, int start, int end;
        start < end ==>
          are_elements_unique(arr, start, end) ==
            (\forall integer k; start <= k < end ==> arr[k] != arr[end]) &&
            are_elements_unique(arr, start, end - 1);

    // Rule II.2: Helper axiom for `are_elements_unique` when an element is found duplicate.
    // If arr[idx] == arr[idx2] for some idx, idx2 in range, then not unique.
    axiom unique_helper_duplicate_found{L}:
        \forall int *arr, int start, int end, integer i, integer j;
          start <= i < end && start <= j < end && i != j && arr[i] == arr[j] ==>
            are_elements_unique(arr, start, end) == \false;

    // Rule II.2: Helper axiom for `are_elements_unique` when all elements are distinct.
    // If for all i, j in range, i != j implies arr[i] != arr[j], then unique.
    axiom unique_helper_all_distinct{L}:
        \forall int *arr, int start, int end;
          (\forall integer i, integer j; start <= i < end && start <= j < end && i != j ==> arr[i] != arr[j]) ==>
            are_elements_unique(arr, start, end) == \true;
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent out-of-bounds access.
  requires \valid_read_range(arr, 0, n - 1);

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return.
  ensures (are_elements_unique(arr, 0, n - 1)) <==> (result == 1);
*/
int are_all_elements_different(int *arr, int n) {
    if (n <= 1) {
        return 1; // An empty or single-element array has all different elements.
    }

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==>
                       (\forall integer l; 0 <= l < k ==> arr[k] != arr[l]);
      loop invariant are_elements_unique(arr, 0, i - 1); // Helper for the overall unique property.
      loop assigns i;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant 0 <= j <= i;
          loop invariant \forall integer k; 0 <= k < j ==> arr[k] != arr[i];
          loop assigns j;
          loop variant i - j;
        */
        for (int j = 0; j < i; j++) {
            if (arr[i] == arr[j]) {
                return 0; // Found a duplicate.
            }
        }
    }

    return 1; // No duplicates found.
}
