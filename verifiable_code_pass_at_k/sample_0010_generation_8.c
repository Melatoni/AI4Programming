// Task ID: 10
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule I.3: Array pointer decay, use correct type for `arr`.
*/
/*@
  axiomatic MinElements {
    logic integer min_val_in_range(int *arr, int start, int end);
    logic integer min_idx_in_range(int *arr, int start, int end);

    axiom min_val_base:
      \forall int *arr, int start;
        min_val_in_range(arr, start, start) == arr[start];

    axiom min_val_rec:
      \forall int *arr, int start, int end;
        start < end ==>
        min_val_in_range(arr, start, end) ==
          (if arr[start] < min_val_in_range(arr, start + 1, end)
           then arr[start]
           else min_val_in_range(arr, start + 1, end));

    axiom min_idx_base:
      \forall int *arr, int start;
        min_idx_in_range(arr, start, start) == start;

    axiom min_idx_rec:
      \forall int *arr, int start, int end;
        start < end ==>
        min_idx_in_range(arr, start, end) ==
          (if arr[start] < arr[min_idx_in_range(arr, start + 1, end)]
           then start
           else min_idx_in_range(arr, start + 1, end));

    // Helper axiom: The minimum value found must be one of the elements in the range.
    axiom min_val_exists:
      \forall int *arr, int start, int end;
        start <= end ==>
        \exists integer k; start <= k <= end && min_val_in_range(arr, start, end) == arr[k];

    // Helper axiom: The index of the minimum value must be within the range.
    axiom min_idx_valid:
      \forall int *arr, int start, int end;
        start <= end ==>
        start <= min_idx_in_range(arr, start, end) <= end;

    // Helper axiom: The value at the minimum index is indeed the minimum value.
    axiom min_idx_val_consistency:
      \forall int *arr, int start, int end;
        start <= end ==>
        arr[min_idx_in_range(arr, start, end)] == min_val_in_range(arr, start, end);
  }
*/

/*@
  requires N >= 0;
  requires K >= 0;
  requires K <= N;
  requires \valid_read(data + (0..N-1));
  requires \valid(smallest_elements + (0..K-1)); // Ensure output array is valid to write to.

  // Rule II.5: Prevent overflow for large N or K if elements were summed, though not needed here.
  // This function modifies 'data' in place via selection sort.
  assigns data[0..N-1], smallest_elements[0..K-1];

  // Post-conditions for the function:
  ensures \forall integer i; 0 <= i < K ==>
            // Each element in smallest_elements must be one of the K smallest from original data.
            // This is implicitly handled by the selection sort placing the smallest K in data[0..K-1]
            // and then copying them.
            \exists integer j; 0 <= j < N && smallest_elements[i] == \old(data[j]);

  ensures \forall integer i; 0 <= i < K ==>
            // Each element in smallest_elements is less than or equal to any element
            // not among the K smallest elements in the original array.
            \forall integer j; K <= j < N ==> \old(data[j]) >= smallest_elements[i];

  ensures \forall integer i; 0 <= i < K ==> smallest_elements[i] == data[i];

  // The first K elements of data should be the K smallest elements from the original data.
  // And these K elements are sorted (ascending).
  ensures \forall integer i; 0 <= i < K ==>
            \forall integer j; 0 <= j < i ==> data[j] <= data[i];

  // The elements data[0..K-1] are the K smallest elements from the original array.
  ensures \forall integer i; 0 <= i < K ==>
            \forall integer j; K <= j < N ==> data[i] <= data[j];
*/
void get_n_smallest_items(int *data, int N, int K, int *smallest_elements) {
    /*@
      loop invariant 0 <= i <= K;
      loop invariant \forall integer x; 0 <= x < i ==>
                        \forall integer y; i <= y < N ==> data[x] <= data[y];
      loop invariant \forall integer x; 0 <= x < i ==>
                        \forall integer y; 0 <= y < x ==> data[y] <= data[x];
      loop invariant \forall integer x; 0 <= x < i ==>
                        \exists integer y; 0 <= y < N && data[x] == \at(data[y], Pre);
      loop invariant \forall integer x; i <= x < N ==>
                        \exists integer y; 0 <= y < N && data[x] == \at(data[y], Pre);
      loop invariant \forall integer x; 0 <= x < N ==>
                        \exists integer y; 0 <= y < N && data[x] == \at(data[y], Pre);
      loop invariant \forall integer x, y; 0 <= x < N && 0 <= y < N && x != y ==>
                        data[x] != data[y] || (\exists integer x_old, y_old; \at(data[x_old], Pre) == data[x] && \at(data[y_old], Pre) == data[y] && x_old != y_old);
      loop assigns i, data[0..N-1];
      loop variant K - i;
    */
    for (int i = 0; i < K; i++) {
        int min_idx = i;
        /*@
          loop invariant i <= j <= N;
          loop invariant i <= min_idx < j;
          loop invariant \forall integer k; i <= k < j ==> data[min_idx] <= data[k];
          loop invariant \exists integer k; i <= k < j && data[min_idx] == data[k];
          loop assigns j, min_idx;
          loop variant N - j;
        */
        for (int j = i + 1; j < N; j++) {
            if (data[j] < data[min_idx]) {
                min_idx = j;
            }
        }

        // Swap data[i] and data[min_idx]
        /*@
          requires 0 <= i < N;
          requires 0 <= min_idx < N;
          assigns data[i], data[min_idx];
          ensures data[i] == \old(data[min_idx]);
          ensures data[min_idx] == \old(data[i]);
        */
        {
            int temp = data[i];
            data[i] = data[min_idx];
            data[min_idx] = temp;
        }
    }

    /*@
      loop invariant 0 <= i <= K;
      loop assigns i, smallest_elements[0..K-1];
      loop variant K - i;
    */
    for (int i = 0; i < K; i++) {
        smallest_elements[i] = data[i];
    }
}
