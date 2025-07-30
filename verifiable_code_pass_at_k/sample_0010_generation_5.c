// Task ID: 10
// Generation: 5

/*@
  // Axiomatic block for recursive logic to define properties of arrays.
  // Rule II.1: Using recursive logic instead of \sum.
  axiomatic ArrayProperties {
    logic integer min_val_in_range(int *arr, integer start, integer end);

    axiom min_val_in_range_base{L}:
      \forall int *arr, integer start;
        min_val_in_range(arr, start, start) == arr[start];

    axiom min_val_in_range_rec{L}:
      \forall int *arr, integer start, integer end;
        start < end ==>
        min_val_in_range(arr, start, end) ==
        (if arr[end] < min_val_in_range(arr, start, end - 1)
         then arr[end]
         else min_val_in_range(arr, start, end - 1));

    logic integer max_val_in_range(int *arr, integer start, integer end);

    axiom max_val_in_range_base{L}:
      \forall int *arr, integer start;
        max_val_in_range(arr, start, start) == arr[start];

    axiom max_val_in_range_rec{L}:
      \forall int *arr, integer start, integer end;
        start < end ==>
        max_val_in_range(arr, start, end) ==
        (if arr[end] > max_val_in_range(arr, start, end - 1)
         then arr[end]
         else max_val_in_range(arr, start, end - 1));

    // Rule II.2: Helper axiom for sortedness.
    logic boolean is_sorted(int *arr, integer start, integer end);

    axiom is_sorted_base{L}:
      \forall int *arr, integer start;
        is_sorted(arr, start, start);

    axiom is_sorted_rec{L}:
      \forall int *arr, integer start, integer end;
        start < end ==>
        is_sorted(arr, start, end) <==> (arr[end-1] <= arr[end] && is_sorted(arr, start, end - 1));

    // Helper axiom for partition property
    logic boolean is_partitioned(int *arr, integer len, integer k);

    axiom is_partitioned_def{L}:
      \forall int *arr, integer len, integer k;
        0 <= k <= len ==>
        is_partitioned(arr, len, k) <==>
        (\forall integer i; 0 <= i < k ==>
          (\forall integer j; k <= j < len ==> arr[i] <= arr[j]));
  }
*/

/*@
  requires 0 <= len;
  requires 0 <= k <= len;
  requires \valid_read(data + (0..len-1));
  requires \valid(result + (0..k-1));
  requires \separated(data + (0..len-1), result + (0..k-1));

  // The function modifies the 'data' array in place to find the k-th smallest element
  // and then copies the smallest k elements.
  assigns data[0..len-1], result[0..k-1];

  // Ensures that the first k elements of 'data' are the k smallest elements from the original 'data' array,
  // and these are copied to 'result' in sorted order.
  ensures is_sorted(result, 0, k - 1);
  ensures \forall integer i; 0 <= i < k ==> \exists integer j; 0 <= j < len && result[i] == \old(data[j]);
  ensures \forall integer i; k <= i < len ==> \old(data[i]) >= max_val_in_range(result, 0, k-1);
  ensures \forall integer i; 0 <= i < k ==> \old(data[i]) <= min_val_in_range(\old(data), k, len-1);
  ensures is_partitioned(data, len, k); // After partitioning, first k elements are smallest
  ensures \forall integer i; 0 <= i < k ==> result[i] == data[i]; // Result contains the partitioned elements
*/
void get_n_smallest_items(int *data, int len, int *result, int k) {
    if (k == 0) {
        return; // Nothing to copy if k is 0
    }

    // Partition the array using a quickselect-like approach to find the k-th smallest element
    // Such that elements data[0...k-1] are the smallest k elements.
    int left = 0;
    int right = len - 1;

    /*@
      loop invariant 0 <= left <= right + 1;
      loop invariant -1 <= right <= len - 1;
      loop invariant left <= k;
      loop invariant right >= k - 1;

      // Invariant for partitioning:
      // Elements to the left of 'left' are known to be smaller than the pivot (which is eventually at 'k-1')
      // Elements to the right of 'right' are known to be larger than the pivot.
      // The goal is to shrink the search space [left, right] until it contains the element at index k-1.
      loop invariant \forall integer i; 0 <= i < left ==> \forall integer j; right <= j < len ==> data[i] <= data[j];
      loop invariant \forall integer i; 0 <= i < left ==> data[i] <= data[k-1];
      loop invariant \forall integer i; right < i < len ==> data[i] >= data[k-1];
      loop invariant k >= 0;
      loop invariant k <= len;

      loop assigns left, right, data[0..len-1];
      loop variant right - left;
    */
    while (left <= right) {
        // Simple pivot selection: middle element
        int pivot_index = left + (right - left) / 2;
        int pivot_value = data[pivot_index];

        // Partitioning step (Lomuto partition scheme)
        int store_index = left;
        int p_idx = pivot_index;

        // Move pivot to end
        {
          int temp = data[p_idx];
          data[p_idx] = data[right];
          data[right] = temp;
        }

        /*@
          loop invariant left <= i <= right;
          loop invariant left <= store_index <= i;
          loop invariant \forall integer x; left <= x < store_index ==> data[x] <= pivot_value;
          loop invariant \forall integer x; store_index <= x < i ==> data[x] > pivot_value;
          loop invariant data[right] == pivot_value; // Pivot is temporarily at the end
          loop invariant \forall integer x; 0 <= x < left ==> \forall integer y; right < y < len ==> data[x] <= data[y];
          loop invariant \forall integer x; 0 <= x < left ==> data[x] <= pivot_value;
          loop invariant \forall integer x; right < x < len ==> data[x] >= pivot_value;

          loop assigns i, store_index, data[0..len-1];
          loop variant i - left;
        */
        for (int i = left; i < right; ++i) {
            if (data[i] < pivot_value) {
                int temp = data[store_index];
                data[store_index] = data[i];
                data[i] = temp;
                store_index++;
            }
        }

        // Move pivot to its final sorted position
        {
          int temp = data[store_index];
          data[store_index] = data[right];
          data[right] = temp;
        }

        if (store_index == k - 1) {
            // Found the k-th smallest element
            break;
        } else if (store_index < k - 1) {
            left = store_index + 1;
        } else { // store_index > k - 1
            right = store_index - 1;
        }
    }

    // After the loop, the first k elements of 'data' are the smallest k elements.
    // Now, copy them to 'result' and sort 'result'.

    // Copy the first k elements to result
    /*@
      loop invariant 0 <= i <= k;
      loop invariant \forall integer j; 0 <= j < i ==> result[j] == data[j];
      loop assigns i, result[0..k-1];
      loop variant k - i;
    */
    for (int i = 0; i < k; ++i) {
        result[i] = data[i];
    }

    // Sort the 'result' array using bubble sort (or any simple sort for small k)
    /*@
      loop invariant 0 <= i <= k;
      loop invariant is_sorted(result, i, k-1);
      loop invariant \forall integer x; 0 <= x < i ==> \forall integer y; i <= y < k ==> result[x] <= result[y];
      loop assigns i, result[0..k-1];
      loop variant k - i;
    */
    for (int i = 0; i < k - 1; ++i) {
        /*@
          loop invariant i < j <= k;
          loop invariant is_sorted(result, i, j-1);
          loop invariant \forall integer x; 0 <= x < i ==> \forall integer y; i <= y < k ==> result[x] <= result[y];
          loop assigns j, result[0..k-1];
          loop variant k - j;
        */
        for (int j = i + 1; j < k; ++j) {
            if (result[i] > result[j]) {
                int temp = result[i];
                result[i] = result[j];
                result[j] = temp;
            }
        }
    }
}
