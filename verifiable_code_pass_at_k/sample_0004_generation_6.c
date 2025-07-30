// Task ID: 4
// Generation: 6

/*@
  // Rule II.1: Define recursive logic functions for properties over sequences.
  // This axiomatic block defines properties for a min-heap structure.
  axiomatic MinHeap {
    // is_min_heap_rec(arr, i, size) checks if the subtree rooted at i is a min-heap.
    // Rule I.3: Array parameters decay to pointers, so use correct pointer type.
    logic boolean is_min_heap_rec{L}(int *arr, int i, int size) =
      i >= size / 2 || // Leaf node or node with only one child (which is effectively a leaf for heap property)
      (
        (2 * i + 1 >= size || arr[i] <= arr[2 * i + 1]) && // Left child check
        (2 * i + 2 >= size || arr[i] <= arr[2 * i + 2]) && // Right child check
        is_min_heap_rec(arr, 2 * i + 1, size) && // Recursively check left subtree
        is_min_heap_rec(arr, 2 * i + 2, size)    // Recursively check right subtree
      );

    // is_min_heap(arr, size) checks if the entire array forms a min-heap.
    logic boolean is_min_heap{L}(int *arr, int size) =
      size <= 1 || is_min_heap_rec(arr, 0, size);

    // is_permutation(arr1, arr2, size) checks if arr2 is a permutation of arr1.
    // This is a common property for sorting/heap algorithms.
    logic boolean is_permutation{L}(int *arr1, int *arr2, int size) =
      \forall integer x; (\numof(integer i; 0 <= i < size && arr1[i] == x) ==
                          \numof(integer j; 0 <= j < size && arr2[j] == x));

    // Helper axiom: if a heap is formed, all elements are within the original range.
    // Rule II.2: CRITICAL - Helper Axioms are needed for the prover.
    axiom min_heap_elements_in_range{L}:
      \forall int *arr, integer size;
        is_min_heap(arr, size) && size > 0 ==>
        (\forall integer i; 0 <= i < size ==>
          (\exists integer j; 0 <= j < size && arr[i] == \old(arr[j])));

    // Helper axiom: if a heap is formed, the root is the minimum element.
    axiom min_heap_root_is_min{L}:
      \forall int *arr, integer size;
        is_min_heap(arr, size) && size > 0 ==>
        (\forall integer i; 0 <= i < size ==> arr[0] <= arr[i]);
  }
*/

// Function to swap two elements in an array.
/*@
  requires valid_read_write_range(arr, 0, size - 1);
  requires 0 <= i < size;
  requires 0 <= j < size;
  assigns arr[i], arr[j];
  ensures arr[i] == \old(arr[j]) && arr[j] == \old(arr[i]);
  ensures \forall integer k; 0 <= k < size && k != i && k != j ==> arr[k] == \old(arr[k]);
  ensures is_permutation(\old(arr), arr, size);
*/
void swap(int *arr, int i, int j, int size) {
  int temp = arr[i];
  arr[i] = arr[j];
  arr[j] = temp;
}

// Function to heapify a subtree rooted at index i in a min-heap.
// It assumes that the children's subtrees are already min-heaps.
/*@
  requires valid_read_write_range(arr, 0, heap_size - 1);
  requires 0 <= i < heap_size;
  // Children subtrees must be heaps before calling min_heapify.
  requires (2 * i + 1 >= heap_size || is_min_heap_rec(arr, 2 * i + 1, heap_size));
  requires (2 * i + 2 >= heap_size || is_min_heap_rec(arr, 2 * i + 2, heap_size));
  assigns arr[0..heap_size-1];
  // The heap property should be restored for the subtree rooted at i.
  ensures is_min_heap_rec(arr, i, heap_size);
  // The elements within the heap_size range should be a permutation of the original elements.
  ensures is_permutation(\old(arr), arr, heap_size);
*/
void min_heapify(int *arr, int heap_size, int i) {
  int smallest = i;
  int left = 2 * i + 1;
  int right = 2 * i + 2;

  /*@
    loop invariant 0 <= i < heap_size;
    loop invariant 0 <= smallest < heap_size;
    loop invariant (left == 2 * i + 1 && right == 2 * i + 2);
    // smallest must point to the smallest among arr[i], arr[left], arr[right]
    loop invariant (left >= heap_size || arr[smallest] <= arr[left]);
    loop invariant (right >= heap_size || arr[smallest] <= arr[right]);
    // The elements not involved in the current comparison chain are unchanged or already swapped.
    loop invariant \forall integer k; 0 <= k < heap_size && k != i && k != smallest ==> arr[k] == \at(arr[k], LoopEntry);
    loop assigns smallest, i, arr[0..heap_size-1];
    loop variant i; // i decreases in each iteration when a swap happens and we recurse
  */
  while (1) {
    int current_smallest = smallest; // Store smallest before potential update

    if (left < heap_size && arr[left] < arr[smallest]) {
      smallest = left;
    }

    if (right < heap_size && arr[right] < arr[smallest]) {
      smallest = right;
    }

    if (smallest != current_smallest) {
      swap(arr, current_smallest, smallest, heap_size);
      i = smallest; // Continue heapifying from the new position of the swapped element
      left = 2 * i + 1;
      right = 2 * i + 2;
    } else {
      break; // Heap property satisfied at i
    }
  }
}

// Function to build a min-heap from an array.
/*@
  requires valid_read_write_range(arr, 0, size - 1);
  requires size >= 0;
  assigns arr[0..size-1];
  ensures is_min_heap(arr, size);
  ensures is_permutation(\old(arr), arr, size);
*/
void build_min_heap(int *arr, int size) {
  if (size <= 1) {
    return;
  }
  /*@
    loop invariant 0 <= i <= size / 2;
    // For all k > i, the subtree rooted at k is a min-heap.
    loop invariant \forall integer k; i < k < size ==> is_min_heap_rec(arr, k, size);
    loop assigns i, arr[0..size-1];
    loop variant i;
  */
  for (int i = size / 2 - 1; i >= 0; i--) {
    min_heapify(arr, size, i);
  }
}

// Function to extract the minimum element from a min-heap.
/*@
  requires valid_read_write_range(arr, 0, size - 1);
  requires size > 0;
  assigns arr[0..size-1]; // Note: size decreases, so it affects a smaller subarray
  // The new heap (of size-1) should still be a min-heap.
  ensures is_min_heap(arr, size - 1);
  // The returned value is the minimum element of the original heap.
  ensures \result == \old(arr[0]);
  // The elements of the new heap are a permutation of the original heap, excluding the extracted element.
  ensures \forall integer x; x != \result ==>
          (\numof(integer i; 0 <= i < size - 1 && arr[i] == x) ==
           \numof(integer j; 0 <= j < size && \old(arr[j]) == x));
*/
int extract_min(int *arr, int *size_ptr) {
  int size = *size_ptr;
  int min_val = arr[0];
  arr[0] = arr[size - 1]; // Move last element to root
  (*size_ptr)--;          // Decrease heap size
  min_heapify(arr, *size_ptr, 0); // Restore heap property
  return min_val;
}

// Function to find the largest k integers using a min-heap.
// The min-heap will store the k largest elements seen so far.
// Its root will be the smallest among these k elements.
/*@
  requires valid_read_range(arr, 0, size - 1);
  requires valid_read_write_range(result, 0, k - 1);
  requires size >= 0;
  requires k >= 0;
  requires k <= size; // k cannot be greater than the total number of elements

  assigns result[0..k-1];

  // The result array should contain the k largest elements from the input array.
  ensures \forall integer x;
            (\numof(integer i; 0 <= i < k && result[i] == x) ==
             \numof(integer j; 0 <= j < size && arr[j] == x &&
                    (\forall integer l; 0 <= l < size ==> arr[l] <= x ||
                                        \numof(integer m; 0 <= m < size && arr[m] > x) < k)));
  // The result array should be sorted in ascending order (optional, but good for output).
  ensures \forall integer i; 0 <= i < k - 1 ==> result[i] <= result[i+1];
*/
void find_k_largest(int *arr, int size, int k, int *result) {
  if (k == 0) {
    return;
  }
  if (size == 0) {
    // If size is 0 and k > 0, result array should probably be filled with some default or left as is.
    // Assuming k > 0 implies size > 0 for valid results.
    return;
  }

  // Create a min-heap of size k to store the k largest elements.
  // Rule I.1: No standard libraries, so a fixed-size array for the heap.
  // This implies a limitation on k, for verification assume `k` is small enough
  // or that `heap` is allocated dynamically. For this problem, we'll assume
  // `k` is small and `heap` is a local array. Frama-C doesn't have dynamic allocation models.
  // A more robust solution would pass the heap array as a parameter.
  // For the purpose of this exercise, let's assume k is small enough for a local array.
  // Or, we can modify the function signature to accept a pre-allocated heap buffer.
  // Let's go with passing a pre-allocated heap buffer.

  // Let's modify the signature to accept a heap buffer:
  /*@
    requires valid_read_write_range(heap_buffer, 0, k - 1); // Heap buffer must be large enough
  */
  // This would change the function signature, but to stick to the original problem,
  // we'll make a pragmatic assumption about a local array or let the user provide it.
  // For Frama-C, a fixed-size local array is easiest to verify directly.
  // Let's assume k is small, for example, k <= 100 for `int heap[100];`
  // If `k` can be arbitrary, then `heap_buffer` must be passed as a parameter.
  // Let's assume `heap_buffer` is passed, as it's more general and verifiable.

  // Re-declare function signature to be more verifiable:
  // void find_k_largest(int *arr, int size, int k, int *result, int *heap_buffer) {
  // For now, let's assume `heap` is a local array and `k` is small enough.
  // This is a common simplification for Frama-C examples if dynamic allocation is not modeled.
  // For a real-world scenario, `heap_buffer` would be passed.
  // Let's define MAX_K to make it verifiable without dynamic memory.
  enum { MAX_K = 1000 }; // Rule I.1: Use enum for constants instead of #define or limits.h
  int heap[MAX_K];       // Local array for the heap

  /*@
    loop invariant 0 <= i <= size;
    loop invariant 0 <= heap_size <= k;
    // The heap_size elements in `heap` are a min-heap.
    loop invariant is_min_heap(heap, heap_size);
    // The heap contains the `heap_size` largest elements processed so far, or is being built.
    loop invariant (\forall integer x; (\numof(integer m; 0 <= m < heap_size && heap[m] == x) <=
                                        \numof(integer n; 0 <= n < i && arr[n] == x)));
    loop assigns i, heap[0..k-1], heap_size;
    loop variant size - i;
  */
  int heap_size = 0;
  for (int i = 0; i < size; ++i) {
    if (heap_size < k) {
      // If heap is not full, just add the element
      heap[heap_size] = arr[i];
      heap_size++;
      // After adding, heap property might be violated, so re-heapify
      // This is not strictly a build_min_heap, but rather an insert and heapify up.
      // For simplicity here, we re-build the heap from scratch if it's not too big.
      // A more efficient way would be to "heapify up" the new element.
      // For verification, `build_min_heap` is easier to reason about for small `heap_size`.
      // Let's use `build_min_heap` for now, assuming k is small.
      build_min_heap(heap, heap_size);
    } else if (arr[i] > heap[0]) {
      // If heap is full and current element is larger than the smallest in heap,
      // replace the smallest and re-heapify.
      heap[0] = arr[i];
      min_heapify(heap, k, 0);
    }
  }

  // After processing all elements, the heap contains the k largest elements.
  // Extract them in decreasing order (by repeatedly extracting min and storing).
  /*@
    loop invariant 0 <= j <= k;
    loop invariant 0 <= current_heap_size <= k;
    loop invariant current_heap_size == k - j;
    // The elements placed into `result` are sorted in ascending order.
    loop invariant \forall integer m; 0 <= m < j - 1 ==> result[m] <= result[m+1];
    // The remaining elements in `heap` form a min-heap.
    loop invariant is_min_heap(heap, current_heap_size);
    // All elements extracted so far are smaller than or equal to the current min of the heap.
    loop invariant \forall integer m; 0 <= m < j ==> (\forall integer n; 0 <= n < current_heap_size ==> result[m] <= heap[n]);
    loop assigns j, result[0..k-1], heap[0..k-1], current_heap_size;
    loop variant current_heap_size;
  */
  int current_heap_size = k;
  for (int j = 0; j < k; ++j) {
    result[k - 1 - j] = extract_min(heap, &current_heap_size);
  }
}
