// Task ID: 10
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1, II.2: Recursive logic for complexity, helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Axiomatic definition for checking if an element is in a sorted array up to a certain index.
  axiomatic ElementInSortedArray {
    logic boolean is_in_sorted_array_prefix(int val, int* arr, int len, int current_idx);

    axiom is_in_sorted_array_prefix_base:
      \forall int val, int* arr, int len;
        0 <= len ==> is_in_sorted_array_prefix(val, arr, len, 0) <==> (arr[0] == val);

    axiom is_in_sorted_array_prefix_recursive:
      \forall int val, int* arr, int len, integer current_idx;
        0 <= current_idx < len ==>
        is_in_sorted_array_prefix(val, arr, len, current_idx) <==>
        (arr[current_idx] == val || is_in_sorted_array_prefix(val, arr, len, current_idx - 1));

    // Helper axiom: If an element is in the prefix, it is also in the full array.
    axiom is_in_sorted_array_prefix_helper_1:
      \forall int val, int* arr, int len, integer current_idx;
        0 <= current_idx < len && is_in_sorted_array_prefix(val, arr, len, current_idx) ==>
        \exists integer k; 0 <= k <= current_idx && arr[k] == val;

    // Helper axiom: If all elements in a prefix are distinct, and val is not in prefix, then val is distinct from prefix.
    axiom is_in_sorted_array_prefix_helper_2:
      \forall int* arr, int len, integer current_idx;
        0 <= current_idx < len &&
        (\forall integer i, j; 0 <= i < j <= current_idx ==> arr[i] != arr[j]) ==>
        (\forall int val; !is_in_sorted_array_prefix(val, arr, len, current_idx) ==>
          (\forall integer k; 0 <= k <= current_idx ==> arr[k] != val));
  }
*/


/*@
  // Axiomatic definition for checking if an array is sorted in non-decreasing order.
  axiomatic SortedArray {
    logic boolean is_sorted(int* arr, int len);

    axiom is_sorted_base:
      \forall int* arr, int len;
        len <= 1 ==> is_sorted(arr, len);

    axiom is_sorted_recursive:
      \forall int* arr, int len;
        len > 1 ==> is_sorted(arr, len) <==> (arr[len - 2] <= arr[len - 1] && is_sorted(arr, len - 1));

    // Helper axiom: If an array is sorted, any two elements are ordered.
    axiom is_sorted_helper:
      \forall int* arr, int len, integer i, integer j;
        0 <= i < j < len && is_sorted(arr, len) ==> arr[i] <= arr[j];
  }
*/

/*@
  // Axiomatic definition for checking if all elements in an array are distinct.
  axiomatic DistinctElements {
    logic boolean has_distinct_elements(int* arr, int len);

    axiom has_distinct_elements_base:
      \forall int* arr, int len;
        len <= 1 ==> has_distinct_elements(arr, len);

    axiom has_distinct_elements_recursive:
      \forall int* arr, int len;
        len > 1 ==> has_distinct_elements(arr, len) <==>
        (\forall integer i; 0 <= i < len - 1 ==> arr[i] != arr[len - 1]) && has_distinct_elements(arr, len - 1);
  }
*/

/*@
  requires dataset_size >= 0;
  requires n >= 0;
  requires n <= dataset_size; // The number of smallest items cannot exceed the dataset size.
  requires \valid_read(dataset + (0..dataset_size-1));
  requires \valid(result + (0..n-1));
  assigns result[0..n-1];

  // Postconditions:
  // 1. The result array contains `n` elements.
  // 2. The result array is sorted in non-decreasing order.
  ensures is_sorted(result, n);

  // 3. All elements in `result` are from `dataset`.
  ensures \forall integer k; 0 <= k < n ==> (\exists integer i; 0 <= i < dataset_size && result[k] == dataset[i]);

  // 4. For any element in `result`, there are at most `n-1` elements in `dataset` that are smaller than it.
  //    This ensures that the elements in `result` are indeed among the smallest.
  ensures \forall integer k; 0 <= k < n ==>
    (\num_of integer i; 0 <= i < dataset_size && dataset[i] < result[k]) <= n - 1;

  // 5. If `n > 0`, the largest element in `result` is less than or equal to any element in `dataset`
  //    that is NOT in `result` AND is not smaller than any element already selected.
  //    This is a stronger property ensuring the 'smallest' criteria.
  ensures n > 0 ==>
    \forall integer val_dataset;
      0 <= val_dataset < dataset_size &&
      !is_in_sorted_array_prefix(dataset[val_dataset], result, n, n-1) ==>
      result[n-1] <= dataset[val_dataset];
*/
void get_n_smallest_items(int* dataset, int dataset_size, int* result, int n) {
    if (n == 0) {
        return; // No items to get.
    }

    // Initialize result with the first n elements of the dataset.
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> result[k] == dataset[k];
      loop assigns i, result[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        result[i] = dataset[i];
    }

    // Simple bubble sort to sort the initial `n` elements.
    // A more efficient sort (like quicksort or heapsort) would be better in practice,
    // but bubble sort is easier to verify for this example.
    /*@
      loop invariant 0 <= i < n;
      loop invariant \forall integer k; 0 <= k < i ==> result[k] <= result[i]; // Elements before i are less than or equal to result[i]
      loop invariant \forall integer x; i <= x < n ==> \forall integer y; x < y < n ==> result[x] <= result[y]; // Suffix is sorted
      loop invariant has_distinct_elements(result, n); // Assuming distinct elements for simpler proof, can be relaxed
      loop invariant \forall integer k; 0 <= k < n ==> (\exists integer l; 0 <= l < n && result[k] == \at(dataset, Pre)[l]); // All elements in result are from original initial n
      loop assigns i, j, result[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n - 1; ++i) {
        /*@
          loop invariant i < j < n;
          loop invariant \forall integer x; i <= x < j ==> result[x] <= result[j];
          loop invariant \forall integer x; j <= x < n ==> result[j] <= result[x];
          loop invariant \forall integer x; 0 <= x < i ==> result[x] <= result[i];
          loop invariant has_distinct_elements(result, n);
          loop invariant \forall integer k; 0 <= k < n ==> (\exists integer l; 0 <= l < n && result[k] == \at(dataset, Pre)[l]);
          loop assigns j, result[0..n-1];
          loop variant n - j;
        */
        for (int j = i + 1; j < n; ++j) {
            if (result[i] > result[j]) {
                int temp = result[i];
                result[i] = result[j];
                result[j] = temp;
            }
        }
    }

    // Now, `result` contains the `n` smallest elements from the *first `n`* elements of `dataset`, and it's sorted.
    // Iterate through the rest of the dataset.
    /*@
      loop invariant n <= i <= dataset_size;
      loop invariant is_sorted(result, n); // result array remains sorted
      loop invariant \forall integer k; 0 <= k < n ==> (\exists integer l; 0 <= l < i && result[k] == dataset[l]); // All elements in result are from dataset[0..i-1]
      loop invariant \forall integer k; 0 <= k < n ==>
        (\num_of integer x; 0 <= x < i && dataset[x] < result[k]) <= n - 1; // n-1 smaller elements in dataset[0..i-1]

      // For any element in `result`, it is smaller than or equal to any element processed so far
      // that is not already in `result` (if it was smaller, it would have been swapped in).
      loop invariant \forall integer k; 0 <= k < n ==>
        \forall integer l; 0 <= l < i && !is_in_sorted_array_prefix(dataset[l], result, n, n-1) ==>
          result[k] <= dataset[l];

      loop assigns i, result[0..n-1];
      loop variant dataset_size - i;
    */
    for (int i = n; i < dataset_size; ++i) {
        // If the current dataset element is smaller than the largest in result
        if (dataset[i] < result[n - 1]) {
            // Replace the largest element in result with the new smaller element
            result[n - 1] = dataset[i];

            // Re-sort the result array to maintain the sorted property.
            // This is an insertion sort step.
            /*@
              loop invariant 0 <= j < n;
              loop invariant result[j] <= result[j+1]; // Current and next element sorted
              loop invariant \forall integer k; j < k < n ==> result[k-1] <= result[k]; // Suffix of result is sorted
              loop invariant \forall integer k; 0 <= k < j ==> result[k] <= result[j]; // Prefix of result is sorted
              loop assigns j, result[0..n-1];
              loop variant j;
            */
            for (int j = n - 1; j > 0; --j) {
                if (result[j] < result[j - 1]) {
                    int temp = result[j];
                    result[j] = result[j - 1];
                    result[j - 1] = temp;
                } else {
                    // Array is already sorted up to this point, break.
                    break;
                }
            }
        }
    }
}
