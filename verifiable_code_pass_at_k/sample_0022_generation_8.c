// Task ID: 22
// Generation: 8

/*@
  // Axiomatic block for recursive logic and helper axioms (Rule II.1, II.2)
  axiomatic FirstDuplicate {
    /*@
      // Recursive function to check if a value exists within a prefix of the array
      logic boolean exists_in_prefix(int* arr, int val, int start, int end) =
        (start > end) ? \false :
        (arr[start] == val) ? \true :
        exists_in_prefix(arr, val, start + 1, end);
    */

    /*@
      // Helper axiom: If a value exists in a prefix [0..k], and we extend the prefix to [0..k+1],
      // it still exists in the extended prefix.
      axiom exists_in_prefix_monotonic_true:
        \forall int* arr, int val, integer start, integer end;
          start <= end ==>
          exists_in_prefix(arr, val, start, end) ==>
          exists_in_prefix(arr, val, start, end + 1);
    */

    /*@
      // Helper axiom: If a value does not exist in a prefix [0..k], and we extend the prefix to [0..k+1]
      // and arr[k+1] is not the value, then it still does not exist in the extended prefix.
      axiom exists_in_prefix_monotonic_false:
        \forall int* arr, int val, integer start, integer end;
          start <= end ==>
          !exists_in_prefix(arr, val, start, end) && arr[end + 1] != val ==>
          !exists_in_prefix(arr, val, start, end + 1);
    */
  }
*/

/*@
  requires N >= 0;
  requires \valid_read(arr + (0..N-1));

  assigns \nothing;

  // Rule II.3: The ensures clause uses logical equivalence for boolean-like return.
  // The result is the index 'i' of the first duplicate element.
  // If a duplicate exists, result is the smallest index 'k' such that arr[k]
  // is equal to some arr[j] where j < k.
  // If no duplicate exists, result is -1.
  ensures (\exists integer k; 0 <= k < N && exists_in_prefix(arr, arr[k], 0, k - 1)) <==> (result != -1);
  ensures result != -1 ==> (0 <= result < N && exists_in_prefix(arr, arr[result], 0, result - 1));
  ensures result != -1 ==> (\forall integer k; 0 <= k < result ==> !exists_in_prefix(arr, arr[k], 0, k - 1));
  ensures result == -1 ==> (\forall integer k; 0 <= k < N ==> !exists_in_prefix(arr, arr[k], 0, k - 1));
*/
int find_first_duplicate(int* arr, int N) {
  /*@
    loop invariant 0 <= i <= N;
    // Invariant: No duplicate has been found in the prefix arr[0..i-1]
    loop invariant \forall integer k; 0 <= k < i ==> !exists_in_prefix(arr, arr[k], 0, k - 1);
    loop assigns i;
    loop variant N - i;
  */
  for (int i = 0; i < N; i++) {
    /*@
      // Inner loop to check for duplicates of arr[i] in the prefix arr[0..i-1]
      loop invariant 0 <= j <= i;
      loop invariant \forall integer k; 0 <= k < j ==> arr[k] != arr[i];
      loop assigns j;
      loop variant i - j;
    */
    for (int j = 0; j < i; j++) {
      if (arr[j] == arr[i]) {
        return i; // Found the first duplicate at index i
      }
    }
  }
  return -1; // No duplicates found
}
