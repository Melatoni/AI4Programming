// Task ID: 22
// Generation: 3

/*@
  requires N >= 0;
  // Rule II.5: Ensure array elements are within a reasonable range to prevent overflow issues
  // if they were to be used in arithmetic operations that could overflow.
  // For this problem, elements are just compared, so a wide range is fine.
  requires \forall integer k; 0 <= k < N ==> INT_MIN <= arr[k] <= INT_MAX;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The result is the value of the first duplicate, or 0 if no duplicate.
  // We define "first duplicate" as the element arr[j] such that there exists
  // an i < j with arr[i] == arr[j], and j is the smallest such index.
  ensures ((\exists integer j; 0 <= j < N &&
             (\exists integer i; 0 <= i < j && arr[i] == arr[j]) &&
             (\forall integer k; 0 <= k < j ==>
                (\forall integer l; 0 <= l < k ==> arr[l] != arr[k])))
           <==> (\result != 0)) &&
          (\result != 0 ==>
            (\exists integer j; 0 <= j < N &&
             (\exists integer i; 0 <= i < j && arr[i] == arr[j]) &&
             (\forall integer k; 0 <= k < j ==>
                (\forall integer l; 0 <= l < k ==> arr[l] != arr[k])) &&
             \result == arr[j])) &&
          (\result == 0 ==>
            (\forall integer j; 0 <= j < N ==>
               (\forall integer i; 0 <= i < j ==> arr[i] != arr[j])));
*/
int find_first_duplicate(int arr[], int N) {
  /*@
    loop invariant 0 <= i <= N;
    // Invariant: No duplicate has been found among elements arr[0]...arr[i-1]
    // for the 'first' index j.
    loop invariant \forall integer k; 0 <= k < i ==>
                     (\forall integer l; 0 <= l < k ==> arr[l] != arr[k]);
    loop assigns i;
    loop variant N - i;
  */
  for (int i = 0; i < N; ++i) {
    /*@
      loop invariant 0 <= j <= i;
      // Invariant: arr[j] is not equal to arr[i] for all 0 <= j < k.
      loop invariant \forall integer k_inner; 0 <= k_inner < j ==> arr[k_inner] != arr[i];
      loop assigns j;
      loop variant i - j;
    */
    for (int j = 0; j < i; ++j) {
      if (arr[i] == arr[j]) {
        return arr[i];
      }
    }
  }
  return 0; // No duplicate found
}
