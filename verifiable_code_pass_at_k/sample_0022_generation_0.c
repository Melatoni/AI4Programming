// Task ID: 22
// Generation: 0

/*@
  // Axiomatic block for recursive logic and helper axioms.
  axiomatic FirstDuplicate {
    // Rule II.1: Define recursive logic for properties over sequences.
    // has_duplicate_in_prefix(arr, len, k) is true if there's a duplicate
    // within arr[0...len-1] where one of the duplicates is arr[k].
    logic boolean has_duplicate_in_prefix{L}(int* arr, integer len, integer k) =
      (k > 0 && \exists integer j; 0 <= j < k && arr[j] == arr[k]) ||
      (k > 0 && has_duplicate_in_prefix(arr, len, k-1));

    // Base case for has_duplicate_in_prefix.
    axiom has_duplicate_in_prefix_base{L}:
      \forall int* arr, integer len;
        has_duplicate_in_prefix(arr, len, 0) == \false;

    // Helper axiom (Rule II.2): If a duplicate exists at index 'k', and 'k' is the first,
    // then no duplicate exists in the prefix up to 'k-1'.
    axiom first_duplicate_implies_no_earlier_duplicate{L}:
      \forall int* arr, integer len, integer k;
        0 <= k < len &&
        (\exists integer j; 0 <= j < k && arr[j] == arr[k]) &&
        (\forall integer x; 0 <= x < k ==> !(\exists integer y; 0 <= y < x && arr[y] == arr[x])) ==>
        !has_duplicate_in_prefix(arr, len, k - 1);

    // Rule II.1: Define recursive logic for finding the minimum index of a duplicate.
    // min_duplicate_idx(arr, len) returns the smallest index k such that arr[k] is a duplicate
    // of an element arr[j] where j < k.
    logic integer min_duplicate_idx{L}(int* arr, integer len);

    // Axiom: If there's no duplicate up to index k, then min_duplicate_idx must be greater than k.
    axiom min_duplicate_idx_no_duplicate{L}:
      \forall int* arr, integer len, integer k;
        0 <= k < len && !has_duplicate_in_prefix(arr, len, k) ==>
        min_duplicate_idx(arr, len) > k;

    // Axiom: If there is a duplicate at index k, and it's the first, then min_duplicate_idx is k.
    axiom min_duplicate_idx_is_k{L}:
      \forall int* arr, integer len, integer k;
        0 <= k < len &&
        (\exists integer j; 0 <= j < k && arr[j] == arr[k]) &&
        (\forall integer x; 0 <= x < k ==> !(\exists integer y; 0 <= y < x && arr[y] == arr[x])) ==>
        min_duplicate_idx(arr, len) == k;

    // Axiom: If no duplicate exists in the entire array, min_duplicate_idx is len (or some indicator).
    // This axiom establishes that if no duplicate is found within the array, the function will return -1.
    // We represent 'no duplicate' by min_duplicate_idx being equal to `len`.
    // This allows us to use `len` as a sentinel value for "no duplicate found".
    axiom min_duplicate_idx_not_found{L}:
      \forall int* arr, integer len;
        (\forall integer k; 0 <= k < len ==> !(\exists integer j; 0 <= j < k && arr[j] == arr[k])) ==>
        min_duplicate_idx(arr, len) == len;


    // Axiom: If a duplicate exists, min_duplicate_idx is the smallest such k.
    axiom min_duplicate_idx_exists{L}:
      \forall int* arr, integer len;
        (\exists integer k; 0 <= k < len && (\exists integer j; 0 <= j < k && arr[j] == arr[k])) ==>
        0 <= min_duplicate_idx(arr, len) < len &&
        (\exists integer j; 0 <= j < min_duplicate_idx(arr, len) && arr[j] == arr[min_duplicate_idx(arr, len)]) &&
        (\forall integer x; 0 <= x < min_duplicate_idx(arr, len) ==> !(\exists integer y; 0 <= y < x && arr[y] == arr[x]));

  }
*/

/*@
  requires N >= 0;
  requires \valid_read_range(arr, 0, N - 1);
  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  ensures (\exists integer k; 0 <= k < N && (\exists integer j; 0 <= j < k && arr[j] == arr[k])) <==> (result != -1);

  // If a duplicate exists, result must be the index of the first duplicate.
  ensures (result != -1) ==>
          (0 <= result < N && (\exists integer j; 0 <= j < result && arr[j] == arr[result]) &&
           (\forall integer x; 0 <= x < result ==> !(\exists integer y; 0 <= y < x && arr[y] == arr[x])));

  // If no duplicate exists, result must be -1.
  ensures (result == -1) ==>
          (\forall integer k; 0 <= k < N ==> !(\exists integer j; 0 <= j < k && arr[j] == arr[k]));

  // Connects the return value to the axiomatic logic function.
  ensures (result == -1 && min_duplicate_idx(arr, N) == N) ||
          (result == min_duplicate_idx(arr, N));
*/
int find_first_duplicate(int* arr, int N) {
    /*@
      loop invariant 0 <= i <= N;
      loop invariant \forall integer k; 0 <= k < i ==> !(\exists integer j; 0 <= j < k && arr[j] == arr[k]);
      loop assigns i;
      loop variant N - i;
    */
    for (int i = 0; i < N; ++i) {
        /*@
          loop invariant 0 <= j <= i;
          loop invariant \forall integer x; 0 <= x < j ==> arr[x] != arr[i];
          loop assigns j;
          loop variant i - j;
        */
        for (int j = 0; j < i; ++j) {
            if (arr[j] == arr[i]) {
                return i;
            }
        }
    }
    return -1;
}
