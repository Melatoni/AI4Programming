// Task ID: 10
// Generation: 2

/*@
  // Axiomatic block for recursive logic and helper axioms.
  // Rule II.1, II.2: Recursive logic for properties over sequences.
  // Rule I.3: Array parameters decay to pointers.
*/
/*@
  axiomatic ArrayProperties {
    logic integer is_sorted_up_to{L}(int* arr, integer end);

    axiom is_sorted_up_to_base{L}:
      \forall int* arr, integer end; end <= 1 ==> is_sorted_up_to(arr, end) == 1;

    axiom is_sorted_up_to_recursive{L}:
      \forall int* arr, integer end; end > 1 ==>
        (is_sorted_up_to(arr, end) == (arr[end-2] <= arr[end-1] && is_sorted_up_to(arr, end-1)));

    logic integer is_permutation_of{L}(int* arr1, integer len1, int* arr2, integer len2);

    axiom is_permutation_of_base_empty{L}:
      \forall int* arr1, int* arr2; is_permutation_of(arr1, 0, arr2, 0) == 1;

    // Helper to count occurrences of an element in an array
    logic integer count_occurrences{L}(int* arr, integer len, int val);

    axiom count_occurrences_base{L}:
      \forall int* arr, int val; count_occurrences(arr, 0, val) == 0;

    axiom count_occurrences_recursive{L}:
      \forall int* arr, integer len, int val; len > 0 ==>
        (count_occurrences(arr, len, val) ==
         (if arr[len-1] == val then 1 else 0) + count_occurrences(arr, len-1, val));

    // Axiom for permutation: two arrays are permutations if they have the same length
    // and each element appears the same number of times in both.
    axiom is_permutation_of_def{L}:
      \forall int* arr1, integer len1, int* arr2, integer len2;
        (is_permutation_of(arr1, len1, arr2, len2) ==
         (len1 == len2 &&
          \forall integer i; 0 <= i < len1 ==>
            count_occurrences(arr1, len1, arr1[i]) == count_occurrences(arr2, len2, arr1[i])));

    // Helper axiom for the minimum value in a sorted array
    logic integer min_val_in_sorted{L}(int* arr, integer len);

    axiom min_val_in_sorted_def{L}:
      \forall int* arr, integer len; len > 0 && is_sorted_up_to(arr, len) ==> min_val_in_sorted(arr, len) == arr[0];

    // Helper axiom for all elements being greater than or equal to a value
    logic integer all_greater_equal{L}(int* arr, integer len, int val);

    axiom all_greater_equal_base{L}:
      \forall int* arr, int val; all_greater_equal(arr, 0, val) == 1;

    axiom all_greater_equal_recursive{L}:
      \forall int* arr, integer len, int val; len > 0 ==>
        (all_greater_equal(arr, len, val) == (arr[len-1] >= val && all_greater_equal(arr, len-1, val)));
  }
*/

/*@
  requires dataset_size >= 0;
  requires n >= 0;
  requires \valid_read_array(dataset, dataset_size);
  requires \valid_write_array(smallest_items, n);
  requires n <= dataset_size; // Cannot get more items than available in the dataset

  // Rule II.5: Prevent potential overflow if n * sizeof(int) is too large for memory allocation (though not directly used here).
  // More practically, ensure n is not excessively large to avoid issues with array indexing or subsequent operations.
  requires n <= 100000; // Arbitrary upper bound to avoid excessively large array sizes

  assigns smallest_items[0..n-1];

  // Rule II.3: Ensures clause using logical equivalence for boolean-like functions.
  // The function returns void, so the post-condition is about the state of smallest_items.
  ensures \forall integer i; 0 <= i < n ==> \exists integer j; 0 <= j < dataset_size && dataset[j] == smallest_items[i];
  ensures is_sorted_up_to(smallest_items, n);
  ensures is_permutation_of(smallest_items, n, \old(dataset), n); // The first n elements of dataset are sorted into smallest_items
  // This is the core property: all elements in smallest_items are among the smallest n elements of the original dataset.
  // This requires that all remaining elements in dataset (dataset[n..dataset_size-1]) are greater than or equal to
  // the maximum element in smallest_items.
  ensures (n == 0) || (n > 0 && \forall integer i; n <= i < dataset_size ==> dataset[i] >= smallest_items[n-1]);
*/
void get_n_smallest(int* dataset, int dataset_size, int* smallest_items, int n) {
    // A simple selection sort variant to get the n smallest items.
    // It's not the most efficient, but provable.

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> \exists integer l; 0 <= l < dataset_size && smallest_items[k] == dataset[l];
      loop invariant \forall integer k; 0 <= k < i-1 ==> smallest_items[k] <= smallest_items[k+1]; // smallest_items[0..i-1] is sorted
      loop invariant \forall integer k; 0 <= k < i ==>
        \forall integer l; i <= l < dataset_size ==> smallest_items[k] <= dataset[l]; // All selected items are less than or equal to unselected
      loop invariant \forall integer k; 0 <= k < i ==>
        \forall integer l; i <= l < dataset_size ==> smallest_items[k] <= dataset[l]; // All selected are among smallest
      loop invariant \forall integer k; i <= k < dataset_size ==> \exists integer val; val == dataset[k]; // elements in dataset[i..dataset_size-1] are still in the dataset
      loop assigns i, dataset[0..dataset_size-1], smallest_items[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        int min_val = dataset[i];
        int min_idx = i;

        /*@
          loop invariant i <= j <= dataset_size;
          loop invariant i <= min_idx < j; // min_idx is always within the scanned part
          loop invariant min_val == dataset[min_idx];
          loop invariant \forall integer k; i <= k < j ==> dataset[k] >= min_val;
          loop assigns j, min_val, min_idx, dataset[i..dataset_size-1];
          loop variant dataset_size - j;
        */
        for (int j = i + 1; j < dataset_size; j++) {
            if (dataset[j] < min_val) {
                min_val = dataset[j];
                min_idx = j;
            }
        }

        // Swap dataset[i] and dataset[min_idx]
        int temp = dataset[i];
        dataset[i] = dataset[min_idx];
        dataset[min_idx] = temp;

        smallest_items[i] = dataset[i];
    }
}
