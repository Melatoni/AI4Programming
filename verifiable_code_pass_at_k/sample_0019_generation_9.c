// Task ID: 19
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in requires/ensures.

  // Rule II.5: Prevent runtime errors.
  // Assume array elements are within int range and N is non-negative.
  requires N >= 0;
  requires \valid_read(arr + (0..N-1));

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like function.
  ensures (\exists integer i, j; 0 <= i < j < N && arr[i] == arr[j]) <==> (\result == 1);
*/
int contains_duplicate(int* arr, int N) {
    /*@
      loop invariant 0 <= i <= N;
      loop invariant \forall integer k1, k2; 0 <= k1 < k2 < i ==> arr[k1] != arr[k2];
      loop assigns i;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        /*@
          loop invariant i < j <= N;
          loop invariant \forall integer k; i < k < j ==> arr[i] != arr[k];
          loop assigns j;
          loop variant N - j;
        */
        for (int j = i + 1; j < N; j++) {
            if (arr[i] == arr[j]) {
                return 1; // Duplicate found
            }
        }
    }
    return 0; // No duplicate found
}
