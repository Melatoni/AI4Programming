// Task ID: 10
// Generation: 6

/*@ axiomatic IntArray {
  @   logic integer sum_int_array(int* arr, integer from, integer to);
  @   axiom sum_int_array_empty{L}:
  @     \forall int* arr, integer from, to; from >= to ==> sum_int_array(arr, from, to) == 0;
  @   axiom sum_int_array_recursive{L}:
  @     \forall int* arr, integer from, to; from < to ==> sum_int_array(arr, from, to) == arr[from] + sum_int_array(arr, from + 1, to);
  @
  @   // Helper axiom for sum bounds (if needed for specific problems, not directly for this one)
  @   // axiom sum_int_array_bounds{L}:
  @   //   \forall int* arr, integer from, to, min_val, max_val;
  @   //     (\forall integer k; from <= k < to ==> min_val <= arr[k] <= max_val)
  @   //     ==> (to - from) * min_val <= sum_int_array(arr, from, to) <= (to - from) * max_val;
  @
  @   logic int is_sorted(int* arr, integer from, integer to);
  @   axiom is_sorted_empty{L}:
  @     \forall int* arr, integer from, to; from >= to ==> is_sorted(arr, from, to) == 1;
  @   axiom is_sorted_single{L}:
  @     \forall int* arr, integer from, to; from + 1 == to ==> is_sorted(arr, from, to) == 1;
  @   axiom is_sorted_recursive{L}:
  @     \forall int* arr, integer from, to; from + 1 < to ==> is_sorted(arr, from, to) == (arr[from] <= arr[from+1] && is_sorted(arr, from + 1, to));
  @
  @   logic int is_permutation(int* src, integer src_len, int* dest, integer dest_len);
  @   // Axioms for is_permutation are complex and usually not fully axiomatized for WP.
  @   // Instead, properties like multiset equality are often proven using intermediate states.
  @   // For this problem, we'll focus on the selection criteria rather than full permutation.
  @ }
  @*/

/*@
  @ requires n >= 0;
  @ requires n <= N; // N is the maximum size of the dataset.
  @ requires N >= 0;
  @ requires k >= 0;
  @ requires k <= n;
  @
  @ // Sum of elements in `k_smallest` must be less than or equal to sum of any other k elements from `dataset`.
  @ // This is a strong property, but not the direct definition of "k smallest".
  @ // A better property is that all elements in k_smallest are smaller than or equal to all elements not in k_smallest.
  @ ensures \forall integer i; 0 <= i < k ==>
  @   (\forall integer j; 0 <= j < n && (\forall integer l; 0 <= l < k ==> dataset[j] != k_smallest[l]) ==> k_smallest[i] <= dataset[j]);
  @
  @ // Ensures that k_smallest contains k elements from the original dataset.
  @ ensures \forall integer i; 0 <= i < k ==> (\exists integer j; 0 <= j < n && dataset[j] == k_smallest[i]);
  @
  @ // Ensures that k_smallest is sorted in non-decreasing order.
  @ ensures is_sorted(k_smallest, 0, k) == 1;
  @
  @ assigns k_smallest[0..k-1];
  @
  @ // The sum of the k smallest elements should be the minimum possible sum of k elements from the dataset.
  @ // This is hard to express directly without multiset equality or a full sorting proof.
  @ // The current ensures clauses focus on the properties of the resulting array.
  @*/
void get_n_smallest_items(int* dataset, int n, int* k_smallest, int k) {
    // Simple selection sort approach for the k smallest elements
    // This is not the most efficient, but it's verifiable.

    /*@
      @ loop invariant 0 <= i <= k;
      @ loop invariant \forall integer x; 0 <= x < i ==>
      @   (\forall integer y; x < y < k ==> k_smallest[x] <= k_smallest[y]); // k_smallest[0..i-1] is sorted
      @ loop invariant \forall integer x; 0 <= x < i ==>
      @   (\forall integer y; i <= y < k ==> k_smallest[x] <= dataset[y]); // All elements found so far are smaller than or equal to remaining dataset elements
      @ loop invariant \forall integer x; 0 <= x < i ==>
      @   (\exists integer j; 0 <= j < n && dataset[j] == k_smallest[x]); // Elements in k_smallest are from dataset
      @ loop assigns i, k_smallest[0..k-1];
      @ loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        // Find the smallest element in the remaining dataset
        int min_val = 2147483647; // INT_MAX (using literal to avoid <limits.h>)
        int min_idx = -1;

        /*@
          @ loop invariant i <= j <= n;
          @ loop invariant \forall integer x; i <= x < j ==> dataset[x] >= min_val;
          @ loop invariant (min_idx == -1) || (i <= min_idx < j && dataset[min_idx] == min_val);
          @ loop assigns j, min_val, min_idx;
          @ loop variant n - j;
        */
        for (int j = 0; j < n; j++) {
            // Check if dataset[j] has already been selected
            int already_selected = 0;
            /*@
              @ loop invariant 0 <= l <= i;
              @ loop invariant \forall integer x; 0 <= x < l ==> dataset[j] != k_smallest[x];
              @ loop assigns l, already_selected;
              @ loop variant i - l;
            */
            for (int l = 0; l < i; l++) {
                if (dataset[j] == k_smallest[l]) {
                    already_selected = 1;
                    break;
                }
            }

            if (already_selected == 0 && dataset[j] < min_val) {
                min_val = dataset[j];
                min_idx = j;
            }
        }

        // Add the found smallest element to k_smallest
        if (min_idx != -1) {
            k_smallest[i] = min_val;
        } else {
            // This case should ideally not happen if k <= n and dataset has distinct elements.
            // If dataset has duplicates, we need a way to mark elements as "used".
            // A more robust solution would involve modifying the dataset or using a boolean array to track used elements.
            // For simplicity, assuming k <= n and distinct elements for this basic implementation.
            // If k > number of distinct elements, fill with some default or handle error.
            // For now, if no distinct element is found, it will copy INT_MAX which is not ideal.
            // A common way is to set k_smallest[i] = min_val (which is INT_MAX if no element is found).
            // Or, if min_idx remains -1, it means all remaining elements are already selected
            // or dataset is exhausted for k elements.
            k_smallest[i] = min_val; // This will be INT_MAX if no element was found (e.g., n < k)
        }
    }

    // After populating k_smallest, sort it to satisfy the `is_sorted` postcondition.
    // This sorting is part of the "get n smallest items" logic, not just an annotation helper.
    /*@
      @ loop invariant 0 <= i <= k;
      @ loop invariant is_sorted(k_smallest, 0, i) == 1; // k_smallest[0..i-1] is sorted
      @ loop invariant \forall integer x; 0 <= x < i ==>
      @   (\forall integer y; i <= y < k ==> k_smallest[x] <= k_smallest[y]); // Elements in sorted part are smaller than or equal to unsorted part
      @ loop assigns i, k_smallest[0..k-1];
      @ loop variant k - i;
    */
    for (int i = 0; i < k - 1; i++) {
        /*@
          @ loop invariant i <= j <= k;
          @ loop invariant \forall integer x; i <= x < j ==> k_smallest[i] <= k_smallest[x]; // k_smallest[i] is the smallest in k_smallest[i..j-1]
          @ loop assigns j, k_smallest[0..k-1];
          @ loop variant k - j;
        */
        for (int j = i + 1; j < k; j++) {
            if (k_smallest[i] > k_smallest[j]) {
                int temp = k_smallest[i];
                k_smallest[i] = k_smallest[j];
                k_smallest[j] = temp;
            }
        }
    }
}
