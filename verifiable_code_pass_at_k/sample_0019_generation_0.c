// Task ID: 19
// Generation: 0

/*@
  // Rule II.1: Define recursive logic for properties over arrays.
  // This logic function checks if a duplicate exists within a subarray arr[low..high].
  logic int has_duplicate_in_subarray{L}(int* arr, int low, int high) =
    (low >= high) ? 0 : // Base case: empty or single element subarray has no duplicate
    (if (\exists integer k; low < k <= high && arr[k] == arr[low])
     then 1 // if arr[low] is duplicated in arr[low+1..high]
     else has_duplicate_in_subarray(arr, low + 1, high)); // else check the rest of the subarray

  // Rule II.2: Helper axiom for the recursive logic function.
  // If no duplicate exists in arr[low..high], then it implies no duplicate exists in arr[low+1..high].
  axiom no_duplicate_implies_subarray_no_duplicate{L}:
    \forall int* arr, integer low, high;
      low < high && has_duplicate_in_subarray(arr, low, high) == 0 ==> has_duplicate_in_subarray(arr, low + 1, high) == 0;

  // Rule II.2: Another helper axiom.
  // If a duplicate exists in arr[low+1..high], then it implies a duplicate exists in arr[low..high].
  axiom subarray_duplicate_implies_duplicate{L}:
    \forall int* arr, integer low, high;
      low < high && has_duplicate_in_subarray(arr, low + 1, high) == 1 ==> has_duplicate_in_subarray(arr, low, high) == 1;
*/

/*@
  requires n >= 0;
  requires \valid_read_range(arr, 0, n - 1);

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // Also uses the recursive logic function defined above.
  ensures (has_duplicate_in_subarray(arr, 0, n - 1) == 1) <==> (result == 1);
*/
int contains_duplicate(int* arr, int n) { // Rule I.2: Use int for boolean.
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> has_duplicate_in_subarray(arr, k, n - 1) == 0;
      loop invariant \forall integer x, y; 0 <= x < y < i ==> arr[x] != arr[y]; // All elements processed so far are unique among themselves.

      loop assigns i, j; // Both loop counters are modified.
      loop variant n - i; // Loop variant for outer loop.
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i + 1 <= j <= n;
          loop invariant \forall integer k; i + 1 <= k < j ==> arr[k] != arr[i]; // No duplicate found for arr[i] in arr[i+1..j-1].
          loop assigns j;
          loop variant n - j; // Loop variant for inner loop.
        */
        for (int j = i + 1; j < n; j++) {
            if (arr[i] == arr[j]) {
                return 1;
            }
        }
    }
    return 0;
}
