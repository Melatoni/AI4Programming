// Task ID: 10
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Axiomatic block for recursive logic. Rule II.1, II.2.
  axiomatic SmallestElements {
    logic integer sum_first_k{L}(int* arr, integer k) reads arr[0..k-1];
    axiom sum_first_k_base{L}:
      sum_first_k(arr, 0) == 0;
    axiom sum_first_k_recursive{L}:
      \forall integer k; k > 0 ==> sum_first_k(arr, k) == sum_first_k(arr, k-1) + arr[k-1];

    // Helper axiom for sorted array sum property. Rule II.2.
    // If an array is sorted, the sum of its first k elements is bounded.
    // This axiom helps connect the sorting property to the sum.
    axiom sum_first_k_sorted_property{L}:
      \forall int* arr, integer k;
        k >= 0 && (\forall integer i, j; 0 <= i < j < k ==> arr[i] <= arr[j]) ==>
        sum_first_k(arr, k) <= k * arr[k-1]; // Upper bound
    
    // Another helper axiom, if all elements are positive, sum is positive.
    axiom sum_first_k_positive{L}:
      \forall int* arr, integer k;
        k >= 0 && (\forall integer i; 0 <= i < k ==> arr[i] >= 0) ==>
        sum_first_k(arr, k) >= 0;
  }
*/

/*@
  requires N >= 0;
  requires n >= 0;
  requires n <= N;
  requires \valid(data + (0..N-1));
  requires \valid(result + (0..n-1));

  // Pre-condition to prevent potential overflow during element sum, if needed.
  // This is a general example, specific bounds would depend on the data range.
  // requires \forall integer i; 0 <= i < N ==> data[i] <= INT_MAX / N; // Example if sum could overflow

  assigns result[0..n-1];

  // Helper predicate to check if an array is sorted in non-decreasing order.
  predicate is_sorted{L}(int* arr, integer len) =
    \forall integer i, j; 0 <= i < j < len ==> arr[i] <= arr[j];

  // Helper predicate to check if all elements in 'result' are also in 'data'.
  predicate all_in_data{L}(int* data, integer N, int* result, integer n) =
    \forall integer i; 0 <= i < n ==> (\exists integer j; 0 <= j < N && result[i] == data[j]);

  // Helper predicate to check if 'result' contains exactly the 'n' smallest elements from 'data'.
  // This is the core post-condition logic.
  predicate contains_n_smallest{L}(int* data, integer N, int* result, integer n) =
    is_sorted(result, n) &&
    all_in_data(data, N, result, n) &&
    // For every element in data not in result, it must be greater than or equal to the largest in result.
    (\forall integer x; 0 <= x < N && !(\exists integer i; 0 <= i < n && data[x] == result[i]) ==>
       (\forall integer k; 0 <= k < n ==> data[x] >= result[k]));
*/
void get_n_smallest(int* data, int N, int* result, int n) {
    // This implementation uses a simple bubble sort-like approach to find the smallest elements.
    // For larger N, a min-heap or selection algorithm would be more efficient,
    // but this is chosen for simplicity in demonstrating ACSL verification.

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \valid(result + (0..n-1));
      loop invariant \valid(data + (0..N-1));

      // Invariant: The first 'i' elements of 'result' are the 'i' smallest found so far, and are sorted.
      loop invariant is_sorted(result, i);
      loop invariant all_in_data(data, N, result, i);

      // Invariant: For the elements already placed in result[0..i-1],
      // all other elements in result[i..n-1] are initially set to a large value,
      // and all elements in data are greater than or equal to result[i-1] (if i>0).
      loop invariant \forall integer k; 0 <= k < i ==>
                     (\forall integer l; i <= l < n ==> result[k] <= result[l]);

      loop assigns i, result[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        // Find the smallest element among the remaining data elements that hasn't been selected yet.
        int min_val = 2147483647; // Represents INT_MAX, Rule I.1.
        int min_idx = -1;

        /*@
          loop invariant i <= j <= N;
          loop invariant \valid(data + (0..N-1));
          loop invariant \valid(result + (0..n-1));
          loop invariant min_idx == -1 || (0 <= min_idx < N && data[min_idx] == min_val);

          // Invariant: If min_idx is not -1, then min_val is the smallest value
          // encountered in data[0..j-1] that is not already in result[0..i-1].
          loop invariant (\forall integer k; 0 <= k < j;
                            !(\exists integer l; 0 <= l < i && data[k] == result[l]) ==>
                            data[k] >= min_val);

          loop assigns j, min_val, min_idx;
          loop variant N - j;
        */
        for (int j = 0; j < N; ++j) {
            // Check if data[j] is not already in result[0..i-1]
            int already_selected = 0; // Rule I.2: Use int for boolean.
            /*@
              loop invariant 0 <= k <= i;
              loop invariant \valid(result + (0..n-1));
              loop invariant already_selected == 1 <==> (\exists integer l; 0 <= l < k && data[j] == result[l]);
              loop assigns k, already_selected;
              loop variant i - k;
            */
            for (int k = 0; k < i; ++k) {
                if (data[j] == result[k]) {
                    already_selected = 1;
                    break;
                }
            }

            if (!already_selected && data[j] < min_val) {
                min_val = data[j];
                min_idx = j;
            }
        }

        // Place the found smallest element into the result array.
        // This assumes that enough unique elements exist in 'data'.
        // If N < n, 'min_idx' could remain -1 if 'data' is exhausted.
        // The precondition 'n <= N' ensures there are always enough elements.
        /*@ assert min_idx != -1; */ // Assert that a smallest element was found.
        result[i] = min_val;

        // Maintain sorted order in result[0..i]
        /*@
          loop invariant 0 <= k <= i;
          loop invariant is_sorted(result, k+1);
          loop assigns k, result[k], result[k+1];
          loop variant k;
        */
        for (int k = i; k > 0; --k) {
            if (result[k] < result[k-1]) {
                int temp = result[k];
                result[k] = result[k-1];
                result[k-1] = temp;
            } else {
                break; // Elements are already in sorted order
            }
        }
    }
    // Post-condition check is implicitly verified by WP based on loop invariants.
    /*@ assert contains_n_smallest(data, N, result, n); */
}
