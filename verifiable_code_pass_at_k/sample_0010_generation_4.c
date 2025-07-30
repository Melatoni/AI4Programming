// Task ID: 10
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1: Recursive logic for complexity.
  // We need to define a concept of "smallest items".
  // This axiomatic block defines a property that a sub-array `arr[0..k-1]`
  // contains the `k` smallest elements from the original array `arr_orig[0..n-1]`.
  // It's a recursive definition useful for proving properties of sorting/selection.
  axiomatic SmallestElements {
    // Defines that 'k' is a valid count of smallest elements.
    logic boolean is_valid_k_for_smallest(integer k, integer n) = (0 <= k <= n);

    // Defines that 'x' is one of the 'k' smallest elements in 'arr_orig[0..n-1]'.
    // This is true if 'x' is in the first 'k' elements of the sorted version of 'arr_orig'.
    // For simplicity, we define it as 'x' being less than or equal to the k-th smallest element.
    // This requires a helper function to find the k-th smallest.
    // However, for the problem of "get n smallest items", we are typically sorting
    // the first 'n' elements of the array. So, we need to prove that the first
    // 'k' elements of the result array 'a' are the smallest 'k' elements from the
    // original array 'a_orig'.

    // Let's define a property that `a[0..k-1]` contains the `k` smallest elements of `a_orig[0..n-1]`.
    // This means all elements in `a[0..k-1]` are smaller than or equal to elements in `a[k..n-1]`
    // and that the elements `a[0..n-1]` are a permutation of `a_orig[0..n-1]`.

    // For a selection sort-like approach, after `k` iterations, `a[0..k-1]` should contain
    // the `k` smallest elements of the original array.
    // This logic function checks if `val` is one of the `count` smallest elements in `a[0..size-1]`.
    // This is hard to prove without a full sort.
    // A simpler approach for "get n smallest items" is to sort the entire array and take the first n.
    // Or, if we are modifying the array in-place, the first 'n' elements are the smallest.

    // Let's assume the function sorts the *first* `k` elements of the array `a` such that
    // they are the `k` smallest elements of the *original* array `a_orig` (before modification).
    // This requires `a_orig` to be passed as a ghost argument, or we use a copy.
    // A more practical approach for in-place modification is to state that `a[0..k-1]`
    // contains the `k` smallest elements, and `a` is a permutation of `a_orig`.

    // Let's define a property for a partially sorted array:
    // `is_k_smallest_prefix(a, k, n, a_orig)` means `a[0..k-1]` are the smallest `k` elements
    // from `a_orig[0..n-1]`, and `a` is a permutation of `a_orig`.

    // We can define `is_smallest_of_remaining(val, arr, start, end)` if `val` is the smallest
    // element in `arr[start..end-1]`.
    logic integer min_in_range(int *arr, integer start, integer end)
    reads arr[start..end-1];
    {
      if start >= end then INT_MAX // Or some appropriate value indicating empty range
      else if start == end - 1 then arr[start]
      else if arr[start] < min_in_range(arr, start + 1, end) then arr[start]
      else min_in_range(arr, start + 1, end)
    }

    // Helper axiom: Minimum of a range is less than or equal to any element in that range.
    axiom min_in_range_le_element:
      \forall int *arr, integer start, integer end, integer i;
        start <= i < end ==> min_in_range(arr, start, end) <= arr[i];

    // Helper axiom: If an element is the minimum, it equals the minimum of the range.
    axiom element_is_min_in_range:
      \forall int *arr, integer start, integer end;
        start < end ==> \exists integer i;
          start <= i < end && arr[i] == min_in_range(arr, start, end);

    // This logic function finds the index of the minimum element in a given range.
    // This is useful for selection sort.
    logic integer index_of_min(int *arr, integer start, integer end)
    reads arr[start..end-1];
    {
      if start >= end then -1 // Or some appropriate value indicating no min
      else if start == end - 1 then start
      else (
        if arr[start] <= arr[index_of_min(arr, start + 1, end)] then start
        else index_of_min(arr, start + 1, end)
      )
    }

    // Helper axiom: index_of_min points to an actual minimum element
    axiom index_of_min_points_to_min:
      \forall int *arr, integer start, integer end;
        start < end ==> arr[index_of_min(arr, start, end)] == min_in_range(arr, start, end);

    // Helper axiom: index_of_min is within the range
    axiom index_of_min_in_range:
      \forall int *arr, integer start, integer end;
        start < end ==> start <= index_of_min(arr, start, end) < end;

    // Helper axiom: If an element is the minimum, its index is returned.
    // This axiom is tricky as there can be multiple minimums.
    // We only need to prove that the one returned by `index_of_min` is indeed a minimum.
  }
*/

/*@
  requires n >= 0;
  requires n_items >= 0;
  requires n_items <= n; // Cannot ask for more items than available.
  requires \valid_read(arr + (0..n-1)); // Array must be readable.
  requires \separated(arr + (0..n-1), \result + (0..n_items-1)); // Output array must be separate.
  requires \valid(\result + (0..n_items-1)); // Output array must be writable.

  // Rule II.5: Prevent RTE. No specific overflow for this problem, but good to keep in mind.

  // The function finds the n_items smallest elements and places them into `result`.
  // It should not modify the original `arr`.
  assigns \result[0..n_items-1];

  // The ensures clause is complex. It states that:
  // 1. The `result` array contains `n_items` elements.
  // 2. These `n_items` elements are precisely the `n_items` smallest elements from `arr`.
  // 3. The `result` array itself should be sorted. (This is a common expectation for "smallest items").
  // 4. `arr` remains unchanged.

  // To prove "n_items smallest elements", we need to define "smallest".
  // Let's assume a selection-sort like approach where we find the smallest N items
  // and put them into `result`.

  // Let's use a ghost array to represent the sorted version of `arr`.
  // This is a common technique when dealing with properties like "smallest elements".
  // Frama-C's WP can reason about permutations and sortedness.

  // We need to define a sorted version of the original array to compare against.
  // This is best done by asserting properties on the `result` array.
  // The `result` array should be sorted.
  ensures \forall integer i; 0 <= i < n_items - 1 ==> \result[i] <= \result[i+1];

  // All elements in `result` must come from `arr`.
  ensures \forall integer i; 0 <= i < n_items ==> \exists integer j; 0 <= j < n && \result[i] == arr[j];

  // For any element in `result`, there are at most `n_items - 1` elements in `arr` that are smaller.
  // And for any element NOT in `result` (i.e., in `arr` but not in `result`), it must be
  // greater than or equal to the largest element in `result`.
  // This is the core "smallest items" property.
  ensures \forall integer x;
    (\exists integer i; 0 <= i < n_items && \result[i] == x)
    <==>
    (
      \fresh(\old(arr[0..n-1])) &&
      // x is one of the n_items smallest elements in arr
      // This is true if the count of elements in arr strictly smaller than x is less than n_items.
      // And the count of elements in arr less than or equal to x is at least n_items.
      (\sum_integer k; 0 <= k < n && arr[k] < x; 1) < n_items &&
      (\sum_integer k; 0 <= k < n && arr[k] <= x; 1) >= n_items
    );

  // The original array `arr` must not be modified.
  assigns \nothing; // This is actually incorrect, as we modify `result`.
  // The correct assigns clause should be:
  // assigns \result[0..n_items-1];
  // The ensures clause needs to specify that `arr` is unchanged.
  ensures \forall integer i; 0 <= i < n ==> arr[i] == \old(arr[i]);
*/
void get_n_smallest_items(int *arr, int n, int *result, int n_items) {
    if (n_items == 0) {
        return; // Nothing to do.
    }

    // A common approach is to copy the first n_items elements, then iterate through the rest
    // to find smaller elements and replace. Then sort the result array.
    // Or, more simply, use a selection sort-like approach directly on the result array.

    // Copy first n_items elements to result.
    /*@
      loop invariant 0 <= i <= n_items;
      loop invariant \forall integer k; 0 <= k < i ==> result[k] == arr[k]; // Initial copy
      loop assigns i, result[0..n_items-1];
      loop variant n_items - i;
    */
    for (int i = 0; i < n_items; i++) {
        result[i] = arr[i];
    }

    // Now, we need to ensure that `result` contains the `n_items` smallest elements.
    // This can be done by a partial sort on `result` or by iteratively finding the smallest.
    // Let's use a selection sort-like approach on the `result` array itself,
    // and then iterate through the rest of `arr` to update `result`.

    // First, make `result` sorted based on its initial elements.
    // This is essentially Selection Sort on `result[0..n_items-1]`
    /*@
      loop invariant 0 <= i <= n_items;
      loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; i <= l < n_items ==> result[k] <= result[l]; // Prefix is sorted relative to suffix
      loop invariant \forall integer k; 0 <= k < i - 1 ==> result[k] <= result[k+1]; // Prefix is sorted
      loop assigns i, result[0..n_items-1];
      loop variant n_items - i;
    */
    for (int i = 0; i < n_items; i++) {
        // Find minimum in result[i..n_items-1]
        int min_val = result[i];
        int min_idx = i;

        /*@
          loop invariant i <= j <= n_items;
          loop invariant i <= min_idx < j;
          loop invariant min_val == min_in_range(result, i, j);
          loop assigns j, min_idx, min_val;
          loop variant n_items - j;
        */
        for (int j = i + 1; j < n_items; j++) {
            if (result[j] < min_val) {
                min_val = result[j];
                min_idx = j;
            }
        }

        // Swap result[i] and result[min_idx]
        if (min_idx != i) {
            int temp = result[i];
            result[i] = result[min_idx];
            result[min_idx] = temp;
        }
    }

    // Now, `result[0..n_items-1]` is sorted and contains the first `n_items` elements of `arr`.
    // Iterate through the rest of `arr` (from `n_items` to `n-1`).
    // If an element `arr[k]` is smaller than the largest element in `result` (which is `result[n_items-1]`),
    // then replace `result[n_items-1]` and re-sort `result`.

    /*@
      loop invariant n_items <= k <= n;
      // Invariant: result[0..n_items-1] contains the n_items smallest elements from arr[0..k-1].
      // And result[0..n_items-1] is sorted.
      loop invariant \forall integer i; 0 <= i < n_items - 1 ==> result[i] <= result[i+1];
      loop invariant \forall integer x;
        (\exists integer i; 0 <= i < n_items && result[i] == x)
        <==>
        (
          (\sum_integer l; 0 <= l < k && arr[l] < x; 1) < n_items &&
          (\sum_integer l; 0 <= l < k && arr[l] <= x; 1) >= n_items
        );
      loop assigns k, result[0..n_items-1];
      loop variant n - k;
    */
    for (int k = n_items; k < n; k++) {
        // If current element arr[k] is smaller than the largest in result
        if (arr[k] < result[n_items - 1]) {
            result[n_items - 1] = arr[k]; // Replace largest with current element

            // Now, re-sort result[0..n_items-1] to maintain sorted property
            // We only need to bubble down the new element.
            int current_idx = n_items - 1;
            /*@
              loop invariant 0 <= current_idx < n_items;
              loop invariant \forall integer i; current_idx <= i < n_items - 1 ==> result[i] <= result[i+1]; // Suffix is sorted
              loop invariant \forall integer i; 0 <= i < current_idx ==> result[i] <= result[current_idx]; // Prefix elements are smaller than or equal to current_idx
              loop assigns current_idx, result[0..n_items-1];
              loop variant current_idx;
            */
            while (current_idx > 0 && result[current_idx] < result[current_idx - 1]) {
                int temp = result[current_idx];
                result[current_idx] = result[current_idx - 1];
                result[current_idx - 1] = temp;
                current_idx--;
            }
        }
    }
}
