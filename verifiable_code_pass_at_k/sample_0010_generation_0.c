// Task ID: 10
// Generation: 0

/*@
  // Axiomatic block for recursive logic and helper axioms.
  // Rule II.1: Using recursive logic for properties over sequences.
  // Rule I.3: Array parameters decay to pointers.
*/
/*@ axiomatic IntArray {
  logic integer array_min_val(int* arr, integer len);
  axiom array_min_val_base{L}(int* arr, integer len) =
    \forall integer k; 0 <= k < len ==> array_min_val(arr, len) <= arr[k];

  logic integer array_max_val(int* arr, integer len);
  axiom array_max_val_base{L}(int* arr, integer len) =
    \forall integer k; 0 <= k < len ==> array_max_val(arr, len) >= arr[k];

  // Helper axiom: if all elements are within a range, then min/max are also within range.
  // Rule II.2: CRITICAL - Helper Axioms are a MUST.
  axiom array_min_max_within_range{L}(int* arr, integer len, integer lower, integer upper) =
    (\forall integer k; 0 <= k < len ==> lower <= arr[k] <= upper)
    ==> (lower <= array_min_val(arr, len) && array_max_val(arr, len) <= upper);

  logic boolean is_sorted_ascending(int* arr, integer len);
  axiom is_sorted_ascending_base:
    \forall int* arr, integer len;
      is_sorted_ascending(arr, len) <==> (\forall integer i; 0 <= i < len - 1 ==> arr[i] <= arr[i+1]);

  logic boolean is_permutation(int* arr1, integer len1, int* arr2, integer len2);
  axiom is_permutation_def:
    \forall int* arr1, integer len1, int* arr2, integer len2;
      is_permutation(arr1, len1, arr2, len2) <==>
      (len1 == len2 &&
       (\forall integer val;
          (\numof(integer i; 0 <= i < len1 && arr1[i] == val) ==
           \numof(integer j; 0 <= j < len2 && arr2[j] == val))));
}
*/

/*@
  requires data_size >= 0;
  requires n >= 0;
  requires n <= data_size; // Cannot ask for more items than available
  requires \valid_read(data + (0..data_size-1));
  requires \valid(result + (0..n-1));

  // Rule II.5: Prevent potential overflow if data elements are large.
  // Assuming int is 32-bit, values up to 2^31-1. No direct arithmetic here,
  // but if elements were summed or multiplied, this would be crucial.
  // For sorting, not as critical unless comparison itself overflows (not applicable here).

  assigns result[0..n-1];

  // The result array should contain the n smallest elements from data.
  // This means:
  // 1. The result array is sorted in ascending order.
  // 2. The result array contains elements from the data array.
  // 3. For any element 'x' in result, there are 'n' elements in data
  //    that are less than or equal to 'x'.
  // 4. For any element 'y' in data that is NOT in result, 'y' must be
  //    greater than or equal to the maximum element in result.

  ensures is_sorted_ascending(result, n);
  ensures \forall integer i; 0 <= i < n ==> (\exists integer j; 0 <= j < data_size && result[i] == data[j]);
  ensures \forall integer j; 0 <= j < data_size ==>
    ( (\exists integer i; 0 <= i < n && data[j] == result[i]) || (data[j] >= array_max_val(result, n)) );
  ensures \forall integer k; 0 <= k < n ==>
    (\numof(integer i; 0 <= i < data_size && data[i] <= result[k]) >= k + 1);
*/
void get_n_smallest(int* data, int data_size, int* result, int n) {
    if (n == 0) {
        return; // Nothing to do if n is 0.
    }

    // Initialize result with the first n elements from data
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> result[k] == data[k];
      loop assigns i, result[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        result[i] = data[i];
    }

    // Simple selection sort for the initial 'result' array
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; i <= l < n ==> result[k] <= result[l];
      loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; 0 <= l < data_size ==> result[k] <= data[l]; // This is too strong
      loop invariant \forall integer k; i <= k < n ==> (\exists integer m; 0 <= m < data_size && result[k] == data[m]);
      loop invariant is_permutation(result, n, \old(result), n); // This is not true after initial copy
      loop assigns i, j, result[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n - 1; i++) {
        int min_idx = i;
        /*@
          loop invariant i <= j <= n;
          loop invariant i <= min_idx < j;
          loop invariant \forall integer k; i <= k < j ==> result[min_idx] <= result[k];
          loop assigns j, min_idx;
          loop variant n - j;
        */
        for (int j = i + 1; j < n; j++) {
            if (result[j] < result[min_idx]) {
                min_idx = j;
            }
        }
        // Swap result[i] and result[min_idx]
        int temp = result[i];
        result[i] = result[min_idx];
        result[min_idx] = temp;
    }

    // Now, result[0..n-1] contains the n smallest elements from data[0..n-1]
    // and is sorted. We need to compare with the rest of data.

    /*@
      loop invariant n <= i <= data_size;
      loop invariant is_sorted_ascending(result, n);
      loop invariant \forall integer k; 0 <= k < n ==> (\exists integer m; 0 <= m < i && result[k] == data[m]); // Not true if elements are swapped
      loop invariant \forall integer k; 0 <= k < n ==> (\forall integer l; n <= l < i ==> result[k] <= data[l]); // This is the goal
      loop invariant \forall integer k; 0 <= k < n ==> \forall integer m; n <= m < i ==> result[k] <= data[m];
      loop invariant \forall integer k; 0 <= k < n ==> result[k] <= array_max_val(result, n);
      loop invariant array_max_val(result, n) == (\max integer j; 0 <= j < n; result[j]);
      loop invariant \forall integer k; 0 <= k < n ==> (\exists integer s; 0 <= s < i && data[s] == result[k]);
      loop invariant \forall integer k; n <= k < i ==> data[k] >= array_max_val(result, n);
      loop assigns i, result[0..n-1];
      loop variant data_size - i;
    */
    for (int i = n; i < data_size; i++) {
        // If data[i] is smaller than the largest element in result,
        // it means data[i] should be one of the n smallest.
        if (data[i] < result[n - 1]) {
            result[n - 1] = data[i]; // Replace the largest with data[i]

            // Maintain sorted order by re-inserting data[i] into its correct position
            // using insertion sort logic for the last element.
            /*@
              loop invariant 0 <= j < n;
              loop invariant \forall integer k; j < k < n ==> result[k] >= result[j];
              loop invariant \forall integer k; 0 <= k < j ==> result[k] <= result[j];
              loop invariant \forall integer k; j < k < n ==> result[k] == \old(result[k]); // This is not true
              loop invariant \forall integer k; j < k < n ==> result[k] >= result[j]; // This is the key invariant
              loop assigns j, result[0..n-1];
              loop variant j;
            */
            for (int j = n - 1; j > 0 && result[j] < result[j - 1]; j--) {
                int temp = result[j];
                result[j] = result[j - 1];
                result[j - 1] = temp;
            }
        }
    }
}
