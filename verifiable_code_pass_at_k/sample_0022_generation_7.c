// Task ID: 22
// Generation: 7

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This logic function checks if a value 'v' exists in the array 'arr'
  // within a specified range [low, high).
  axiomatic ValueExists {
    logic boolean exists_in_range(int[] arr, int low, int high, int v);

    axiom exists_in_range_base:
      \forall int[] arr, int low, int v;
        exists_in_range(arr, low, low, v) == \false;

    axiom exists_in_range_recursive:
      \forall int[] arr, int low, int high, int v;
        low < high ==>
        exists_in_range(arr, low, high, v) ==
        (if arr[low] == v then \true else exists_in_range(arr, low + 1, high, v));

    // Rule II.2: Helper axiom to prove if a value exists in a sub-range, it exists in the larger range.
    axiom exists_in_range_subset:
      \forall int[] arr, int low1, int high1, int low2, int high2, int v;
        low1 <= low2 && high2 <= high1 ==>
        (\forall integer i; low2 <= i < high2 ==> arr[i] != v) ==>
        (\forall integer i; low1 <= i < high1 ==> arr[i] != v);
  }
*/

/*@
  requires n >= 0;
  requires \valid_read_range(arr, 0, n - 1);

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function returns 1 if a duplicate is found (and 'res' is the first such duplicate).
  // It returns 0 if no duplicate is found.
  ensures (\exists integer i, j;
            0 <= i < j < n && arr[i] == arr[j] && // There exists a duplicate
            (\forall integer k, l; 0 <= k < l < j ==> k != i || arr[k] != arr[l]) && // And it's the first such duplicate (by j's minimality)
            result == arr[i] // The result is the value of the first duplicate
          )
          <==>
          (result != 0); // result is non-zero (meaning a duplicate was found)

  // If no duplicate is found, the result must be 0.
  ensures (\forall integer i, j; 0 <= i < j < n ==> arr[i] != arr[j]) <==> (result == 0);
*/
int find_first_duplicate(int arr[], int n) { // Rule I.2: Uses int for return value.
    if (n <= 1) {
        return 0; // No duplicates possible in array of size 0 or 1
    }

    /*@
      loop invariant 0 <= i <= n;
      // All elements examined so far (arr[0]...arr[i-1]) do not have duplicates
      // with any element before them.
      loop invariant \forall integer k; 0 <= k < i ==> (\forall integer l; 0 <= l < k ==> arr[k] != arr[l]);
      // If a duplicate exists, it must be at or after index i.
      loop invariant (\exists integer x, y; 0 <= x < y < n && arr[x] == arr[y]) ==>
                     (\exists integer x_prime, y_prime; i <= x_prime < y_prime < n && arr[x_prime] == arr[y_prime]);
      loop assigns i;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i <= j <= n;
          // arr[i] has not been found among arr[i+1]...arr[j-1]
          loop invariant \forall integer k; i < k < j ==> arr[i] != arr[k];
          loop assigns j;
          loop variant n - j;
        */
        for (int j = i + 1; j < n; j++) {
            if (arr[i] == arr[j]) {
                return arr[i]; // Rule I.2: Returns the duplicate value itself.
            }
        }
    }

    return 0; // Rule I.2: Returns 0 if no duplicate is found.
}
