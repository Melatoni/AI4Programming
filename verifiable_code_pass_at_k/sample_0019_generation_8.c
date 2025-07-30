// Task ID: 19
// Generation: 8

/*@
  // Axiomatic definition for checking if a subarray contains a specific value.
  // Rule II.1: Recursive logic for complex properties.
  axiomatic ValueInSubarray {
    logic boolean value_in_subarray{L}(int* arr, int start, int end, int val);

    // Base case: empty subarray
    axiom value_in_subarray_empty{L}:
      orall int* arr, int start, int end, int val;
        start >= end ==> !value_in_subarray(arr, start, end, val);

    // Recursive case 1: value found at start
    axiom value_in_subarray_found{L}:
      orall int* arr, int start, int end, int val;
        start < end && arr[start] == val ==> value_in_subarray(arr, start, end, val);

    // Recursive case 2: value not at start, check rest of subarray
    axiom value_in_subarray_not_found{L}:
      orall int* arr, int start, int end, int val;
        start < end && arr[start] != val ==> (value_in_subarray(arr, start, end, val) <==> value_in_subarray(arr, start + 1, end, val));
  }
*/

/*@
  requires n >= 0;
  requires \valid_read_range(arr, 0, n - 1);
  assigns 
othing;

  // Rule II.3: Ensures clause uses logical equivalence.
  // The function returns 1 if there exists i and j such that 0 <= i < j < n and arr[i] == arr[j].
  // Rule II.1: Using a recursive logic function (value_in_subarray) for the inner check.
  ensures (\exists integer i, j; 0 <= i < j < n && arr[i] == arr[j]) <==> (esult == 1);
*/
int contains_duplicate(int* arr, int n) { // Rule I.2: int for boolean.
    /*@
      loop invariant 0 <= i <= n;
      // For all k from 0 to i-1, no duplicate exists in arr[0..k] compared to arr[0..k-1].
      // This means that arr[0..i-1] contains no duplicates.
      loop invariant orall integer k; 0 <= k < i ==> !\exists integer l; 0 <= l < k && arr[k] == arr[l];
      loop assigns i, j; // i is assigned in the outer loop, j in the inner loop.
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i + 1 <= j <= n;
          // For all k from i+1 to j-1, arr[k] is not equal to arr[i].
          // This means arr[i] is not duplicated in arr[i+1..j-1].
          loop invariant orall integer k; i + 1 <= k < j ==> arr[k] != arr[i];
          loop assigns j;
          loop variant n - j;
        */
        for (int j = i + 1; j < n; j++) {
            if (arr[i] == arr[j]) {
                return 1;
            }
        }
    }
    return 0;
}
