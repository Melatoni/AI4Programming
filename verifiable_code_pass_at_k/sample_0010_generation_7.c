// Task ID: 10
// Generation: 7

/*@
  axiomatic GetSmallest {

    // Rule II.1: Recursive logic function to define the property of an array
    // being sorted up to a certain index 'k'
    logic boolean is_sorted_prefix(int* arr, int k) =
      k <= 1 || (arr[k-2] <= arr[k-1] && is_sorted_prefix(arr, k-1));

    // Rule II.1: Recursive logic function to define the property of an array
    // being sorted in its entirety
    logic boolean is_sorted(int* arr, int len) =
      is_sorted_prefix(arr, len);

    // Rule II.1: Recursive logic function to define the property that a
    // subarray contains only elements from another subarray.
    // This is used to express that the 'n' smallest elements are a permutation
    // of some elements from the original 'data' array.
    logic boolean contains_only_from(int* subset, int subset_len, int* superset, int superset_len) =
      subset_len <= 0 ||
      (\exists integer i; 0 <= i < superset_len && subset[subset_len-1] == superset[i]) &&
      contains_only_from(subset, subset_len-1, superset, superset_len);

    // Rule II.1: Recursive logic function to count occurrences of a value in an array.
    // Used for permutation property: the count of each element must be the same.
    logic integer count_occurrences(int* arr, int len, int val) =
      len <= 0 ? 0 :
      (arr[len-1] == val ? 1 : 0) + count_occurrences(arr, len-1, val);

    // Rule II.2: Helper axiom for count_occurrences to prove that if an element is in
    // both arrays, its count is consistent. This is a crucial property for permutations.
    axiom count_consistency:
      \forall int* subset, int subset_len, int* superset, int superset_len, int val;
        (contains_only_from(subset, subset_len, superset, superset_len) &&
         \forall integer k; 0 <= k < subset_len ==> \exists integer j; 0 <= j < superset_len && subset[k] == superset[j]) ==>
        count_occurrences(subset, subset_len, val) <= count_occurrences(superset, superset_len, val);
  }
*/

/*@
  requires data_len >= 0;
  requires n >= 0;
  requires n <= data_len; // Can't ask for more elements than available
  requires \valid_read_array(data, data_len);
  requires \valid_write_array(result, n);

  // Rule II.5: Prevent potential overflow if n is large and result_len is used in array indexing
  // or if data_len is large. For this problem, it's more about array bounds.
  // The constraints n <= data_len and \valid_array already handle this for indexing.

  assigns result[0..n-1];

  // Rule II.3: Use logical equivalence for boolean-like function (though this one returns void)
  // The post-conditions are the core of the problem.
  ensures is_sorted(result, n); // The 'n' smallest items must be sorted
  ensures \forall integer i; 0 <= i < n ==> \exists integer j; 0 <= j < data_len && result[i] == data[j]; // All results are from data
  ensures contains_only_from(result, n, data, data_len); // All results are from data (alternative formulation)

  // This ensures clause states that for any element in `result`, there are at least `n`
  // elements in `data` that are less than or equal to it, AND for any element not in
  // `result` (from the original `data` set), it must be greater than or equal to
  // the largest element in `result`.
  // This essentially proves that `result` contains the *n smallest* elements.

  // The elements in 'result' are the n smallest elements from 'data'.
  // This means:
  // 1. All elements in 'result' are from 'data'. (covered by contains_only_from)
  // 2. 'result' is sorted. (covered by is_sorted)
  // 3. For any element 'x' in 'result', the number of elements in 'data' less than or equal to 'x'
  //    is at least the number of elements in 'result' less than or equal to 'x'.
  //    And for any element 'y' in 'data' not in 'result', 'y' must be greater than or equal to
  //    the max element in 'result'.

  // A more robust way to specify "n smallest":
  // For any element `x` in `result`, its count in `result` must be less than or equal to its count in `data`.
  // Also, for any element `y` in `data` but not in `result`, it must be greater than or equal to
  // the maximum element in `result` (if `n > 0`).

  // If n > 0, then the maximum element in `result` (which is `result[n-1]` because it's sorted)
  // must be less than or equal to any element in `data` that is NOT among the `n` smallest.
  ensures n == 0 || (\forall integer k; 0 <= k < data_len ==>
    (count_occurrences(data, data_len, data[k]) > count_occurrences(result, n, data[k]) ==> data[k] >= result[n-1]));

  // This ensures clause is crucial for proving "smallest".
  // For any element `x` in `data`, if `x` is not in `result` (or its count in `data` is greater
  // than its count in `result`), then `x` must be greater than or equal to the largest
  // element in `result` (if `n` > 0).
  ensures n == 0 || (\forall integer k; 0 <= k < data_len;
    (count_occurrences(data, data_len, data[k]) > count_occurrences(result, n, data[k])) ==> data[k] >= result[n-1]);
*/
void get_n_smallest(int* data, int data_len, int* result, int n) {
    if (n == 0) {
        return;
    }

    // Initialize result with the first n elements of data
    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> result[k] == data[k];
      loop assigns i, result[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        result[i] = data[i];
    }

    // Simple Bubble Sort to sort the initial 'n' elements in `result`
    // This makes sure `result` is sorted before we start comparing with the rest of `data`.
    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant is_sorted_prefix(result, n - i); // Elements from n-i to n-1 are sorted
      loop invariant \forall integer k; n - i <= k < n ==> \forall integer l; 0 <= l < n - i ==> result[l] <= result[k]; // elements in sorted suffix are greater than or equal to elements in unsorted prefix
      loop assigns i, j, result[0..n-1];
      loop variant i;
    */
    for (int i = 0; i < n - 1; i++) {
        /*@
          loop invariant i <= j && j <= n;
          loop invariant \forall integer k; j <= k < n ==> result[j-1] <= result[k];
          loop assigns j, result[0..n-1];
          loop variant n - j;
        */
        for (int j = n - 1; j > i; j--) {
            if (result[j] < result[j-1]) {
                int temp = result[j];
                result[j] = result[j-1];
                result[j-1] = temp;
            }
        }
    }

    // Iterate through the rest of the data array
    /*@
      loop invariant n <= i && i <= data_len;
      // The crucial invariant: result[0..n-1] contains the n smallest elements encountered so far
      // from data[0..i-1], and result[0..n-1] is sorted.
      loop invariant is_sorted(result, n);
      loop invariant \forall integer k; 0 <= k < n ==> \exists integer l; 0 <= l < i && result[k] == data[l];
      loop invariant \forall integer k; 0 <= k < i;
        (count_occurrences(data, i, data[k]) > count_occurrences(result, n, data[k])) ==> data[k] >= result[n-1];
      loop assigns i, result[0..n-1];
      loop variant data_len - i;
    */
    for (int i = n; i < data_len; i++) {
        // If current data element is smaller than the largest in our result set
        if (data[i] < result[n-1]) {
            // Replace the largest element in result with data[i]
            result[n-1] = data[i];

            // Re-sort the result array (insertion sort for the last element)
            /*@
              loop invariant 0 <= j && j < n;
              loop invariant \forall integer k; j < k < n ==> result[j] <= result[k];
              loop assigns j, result[0..n-1];
              loop variant j;
            */
            for (int j = n - 1; j > 0; j--) {
                if (result[j] < result[j-1]) {
                    int temp = result[j];
                    result[j] = result[j-1];
                    result[j-1] = temp;
                } else {
                    // Optimization: if result[j] is not smaller than result[j-1],
                    // it means the array is sorted up to this point.
                    break;
                }
            }
        }
    }
}
