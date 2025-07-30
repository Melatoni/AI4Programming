// Task ID: 22
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in logic functions if needed.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms are CRITICAL.
  // Rule II.3: ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent runtime errors.

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic HasDuplicate {
    // Defines what it means for a subarray to contain a duplicate.
    // A duplicate exists in arr[0..k-1] if there are i, j such that 0 <= i < j < k and arr[i] == arr[j].
    logic boolean has_duplicate_in_prefix{L}(int* arr, int k) reads arr[0..k-1];

    axiom has_duplicate_in_prefix_base{L}:
      \forall int* arr, integer k; k <= 1 ==> !has_duplicate_in_prefix(arr, k);

    axiom has_duplicate_in_prefix_recursive{L}:
      \forall int* arr, integer k; k > 1 ==>
        (has_duplicate_in_prefix(arr, k) <==>
          (has_duplicate_in_prefix(arr, k - 1) ||
           (\exists integer i; 0 <= i < k - 1 && arr[i] == arr[k - 1])));

    // Helper axiom: if a duplicate exists in arr[0..k-1], it also exists in arr[0..k].
    axiom has_duplicate_in_prefix_monotonic{L}:
      \forall int* arr, integer k;
        has_duplicate_in_prefix(arr, k) ==> has_duplicate_in_prefix(arr, k + 1);

    // Defines what it means for an element at index 'idx' to be the first duplicate.
    // This means arr[idx] is a duplicate, and no element before arr[idx] is a duplicate.
    // An element arr[idx] is a duplicate if it appeared before arr[idx].
    // i.e., \exists i; 0 <= i < idx && arr[i] == arr[idx]
    // And for any k < idx, arr[k] is not a duplicate, meaning:
    // \forall k; 0 <= k < idx ==> (\forall j; 0 <= j < k ==> arr[j] != arr[k])
    logic boolean is_first_duplicate{L}(int* arr, int n, int idx) reads arr[0..n-1];

    // arr[idx] is the first duplicate if:
    // 1. It is a duplicate itself: exists i < idx such that arr[i] == arr[idx]
    // 2. The prefix arr[0..idx-1] has no duplicates.
    axiom is_first_duplicate_def{L}:
      \forall int* arr, integer n, integer idx;
        0 <= idx < n ==>
        (is_first_duplicate(arr, n, idx) <==>
         (\exists integer i; 0 <= i < idx && arr[i] == arr[idx]) &&
         !has_duplicate_in_prefix(arr, idx));
  }
*/

/*@
  requires n >= 0;
  requires \valid_read(arr + (0..n-1));
  assigns \nothing;

  // Rule II.3: ensures clause for boolean-like functions uses <==>.
  ensures (\exists integer k; 0 <= k < n && is_first_duplicate(arr, n, k)) <==> (result != -1);
  ensures (result != -1) ==> (0 <= result < n && is_first_duplicate(arr, n, result));
  ensures (result == -1) ==> (\forall integer k; 0 <= k < n ==> !is_first_duplicate(arr, n, k));
  ensures (result == -1) ==> !has_duplicate_in_prefix(arr, n);
*/
int find_first_duplicate(int* arr, int n) {
    /*@
      loop invariant 0 <= i <= n;
      // The prefix arr[0..i-1] does not contain any duplicates.
      loop invariant !has_duplicate_in_prefix(arr, i);
      // For any element arr[k] with 0 <= k < i, it is not the first duplicate.
      loop invariant \forall integer k; 0 <= k < i ==> !is_first_duplicate(arr, n, k);
      loop assigns i;
      loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        /*@
          loop invariant 0 <= j < i;
          // For any element arr[k] with 0 <= k < j, arr[k] != arr[i].
          loop invariant \forall integer k; 0 <= k < j ==> arr[k] != arr[i];
          loop assigns j;
          loop variant i - j;
        */
        for (int j = 0; j < i; ++j) {
            if (arr[i] == arr[j]) {
                // Found a duplicate. Since the outer loop invariant ensures
                // !has_duplicate_in_prefix(arr, i), and we found arr[j] == arr[i] with j < i,
                // this means arr[i] is the first duplicate.
                return i;
            }
        }
    }
    return -1; // No duplicate found
}
