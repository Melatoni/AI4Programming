// Task ID: 4
// Generation: 1

/*@
  // Rule I.1: No standard libraries like limits.h; use ACSL constants directly.
  // Rule II.5: Prevent potential overflow when accessing array elements.
  requires 0 <= size <= INT_MAX; 
  requires \valid_read(arr + (0..size-1));
  requires \valid(arr + (0..size-1)); // For potential writes during heapify
*/
/*@ axiomatic Swap {
  logic <type> \at_swap{L1, L2}(<type> v, <type>* p);
  axiom swap_def{L1, L2}:
    \forall <type> v, <type>* p;
      \at_swap{L1, L2}(v, p) == (if v == \at(*p, L1) then \at(*p, L2) else \at(v, L1));
}
*/

/*@
  logic integer parent_idx(integer i) = (i - 1) / 2;
  logic integer left_child_idx(integer i) = 2 * i + 1;
  logic integer right_child_idx(integer i) = 2 * i + 2;

  // Rule II.1: Define recursive logic for properties over sequences.
  // This logic function checks if a subarray arr[0..k] satisfies the max-heap property.
  logic boolean is_max_heap_property(int* arr, integer k) =
    \forall integer i;
      0 <= i && left_child_idx(i) <= k ==> arr[i] >= arr[left_child_idx(i)] &&
      0 <= i && right_child_idx(i) <= k ==> arr[i] >= arr[right_child_idx(i)];

  // Helper axiom for is_max_heap_property: A single element is a heap.
  axiom is_max_heap_property_base:
    \forall int* arr; is_max_heap_property(arr, -1);
  axiom is_max_heap_property_base_0:
    \forall int* arr; is_max_heap_property(arr, 0);

  // Helper axiom: If a heap property holds for k, it might hold for k-1 (not strictly needed for WP but good practice)
  axiom is_max_heap_property_recursive:
    \forall int* arr, integer k;
      k >= 0 && is_max_heap_property(arr, k) ==> is_max_heap_property(arr, k-1);

  // Recursive logic to check if a subarray is a max-heap (including parent-child relations).
  // This is a more robust definition for the loop invariant.
  logic boolean is_max_heap(int* arr, integer size) =
    \forall integer i;
      0 <= i && left_child_idx(i) < size ==> arr[i] >= arr[left_child_idx(i)] &&
      0 <= i && right_child_idx(i) < size ==> arr[i] >= arr[right_child_idx(i)];

  // Helper axiom for is_max_heap: empty or single element is a heap.
  axiom is_max_heap_empty: \forall int* arr; is_max_heap(arr, 0);
  axiom is_max_heap_single: \forall int* arr; is_max_heap(arr, 1);

  // Helper axiom: If a heap property holds for size, it holds for any smaller size.
  axiom is_max_heap_sub_array:
    \forall int* arr, integer size, integer sub_size;
      0 <= sub_size <= size && is_max_heap(arr, size) ==> is_max_heap(arr, sub_size);

  // Helper axiom: If a heap property holds for size, and we swap two elements,
  // it might not hold anymore unless it's a specific swap within heapify.
  // (More specific axioms for heapify are defined within the functions)
*/

/*@
  requires size > 0;
  requires 0 <= i < size;
  requires \valid(arr + (0..size-1));
  assigns arr[0..size-1];

  // Ensures that after calling heapify_down, the subtree rooted at i (and its children)
  // satisfies the max-heap property, and arr[0..size-1] is a max-heap.
  // The ensures clause uses the logical equivalence pattern.
  ensures is_max_heap(arr, size);
  ensures \forall integer k; 0 <= k < size ==> (\old(arr[k]) == arr[k] || \old(arr[k]) == \at(arr[0], Pre)); // Elements are preserved or moved
*/
void heapify_down(int* arr, int size, int i) {
    int largest = i;
    int left = 2 * i + 1;
    int right = 2 * i + 2;

    /*@
      loop invariant 0 <= i < size;
      loop invariant 0 <= largest < size;
      loop invariant 0 <= left;
      loop invariant 0 <= right;
      loop invariant \forall integer k; (0 <= k < size && k != i && k != largest && k != left && k != right) ==> arr[k] == \at(arr[k], Pre);
      loop invariant is_max_heap_property(arr, i-1); // Elements before i maintain heap property
      loop invariant \forall integer k; (0 <= k < i && left_child_idx(k) >= size) ==> arr[k] == \at(arr[k], Pre); // Check if this is needed
      loop invariant \forall integer k; (0 <= k < i && right_child_idx(k) >= size) ==> arr[k] == \at(arr[k], Pre); // Check if this is needed

      // The key invariant for heapify_down: the elements from `i+1` to `size-1` (which are children of `i`)
      // and their children *already* satisfy the max-heap property.
      // This is crucial because heapify_down assumes its children are heaps.
      loop invariant is_max_heap(arr, size); // The whole array is a heap, except possibly for subtree at `i`.
      loop invariant \at(arr[i], LoopCurrent) == \at(arr[largest], LoopCurrent) || \at(arr[i], LoopCurrent) == \at(arr[i], LoopEntry); // Only `i` changes.

      // The variant ensures termination: the distance from `i` to the end of the array.
      loop variant size - i;
    */
    while (left < size) {
        if (left < size && arr[left] > arr[largest]) {
            largest = left;
        }
        if (right < size && arr[right] > arr[largest]) {
            largest = right;
        }

        if (largest != i) {
            // Swap arr[i] and arr[largest]
            int temp = arr[i];
            arr[i] = arr[largest];
            arr[largest] = temp;

            i = largest;
            left = 2 * i + 1;
            right = 2 * i + 2;
        } else {
            break; // Heap property satisfied for this subtree
        }
    }
}

/*@
  requires size >= 0;
  requires \valid(arr + (0..size-1));
  assigns arr[0..size-1];
  // Ensures that after calling build_max_heap, the entire array arr[0..size-1] satisfies the max-heap property.
  ensures is_max_heap(arr, size);
*/
void build_max_heap(int* arr, int size) {
    if (size <= 1) {
        return;
    }

    /*@
      loop invariant 0 <= i <= size / 2;
      loop invariant \forall integer k; i < k < size ==> is_max_heap_property(arr, k); // All subtrees starting from i+1 are max-heaps
      loop invariant is_max_heap(arr, size); // The whole array is a heap, except possibly for subtree at `i`.
      loop assigns i, arr[0..size-1]; // `arr` might be modified by heapify_down
      loop variant i;
    */
    for (int i = size / 2 - 1; i >= 0; i--) {
        heapify_down(arr, size, i);
    }
}

/*@
  requires k >= 0;
  requires size >= 0;
  requires size >= k;
  requires \valid(arr + (0..size-1));
  assigns arr[0..size-1];
  // Ensures that the first `k` elements of the array are the `k` largest elements from the original array,
  // and they are sorted in descending order.
  ensures \forall integer i; 0 <= i < k-1 ==> arr[i] >= arr[i+1];
  ensures \forall integer i; 0 <= i < k ==>
    (\exists \set<integer> S;
      \forall integer j; j \in S ==> 0 <= j < size && \at(arr[j], Pre) == arr[i] &&
      \card(S) == (\numof(int m; 0 <= m < size && \at(arr[m], Pre) == arr[i]))); // Check count of elements
  ensures \forall integer i; k <= i < size ==>
    (\forall integer j; 0 <= j < k ==> arr[j] >= arr[i]);
*/
void find_k_largest(int* arr, int size, int k) {
    if (k <= 0 || size == 0) {
        return;
    }

    if (k > size) {
        k = size; // Find all elements if k is too large
    }

    build_max_heap(arr, size); // First, build a max-heap from the entire array

    /*@
      loop invariant 0 <= i <= k;
      loop invariant is_max_heap(arr, size - i); // The remaining part of the array is still a max-heap
      loop invariant \forall integer j; 0 <= j < i ==> arr[j] == \at(arr[j], LoopEntry); // Top `i` elements are the largest and sorted
      loop invariant \forall integer j; 0 <= j < i-1 ==> arr[j] >= arr[j+1]; // The first `i` elements are sorted in descending order
      loop invariant \forall integer j; 0 <= j < i ==> (\forall integer l; i <= l < size ==> arr[j] >= arr[l]); // The first `i` elements are larger than the rest
      loop assigns i, arr[0..size-1];
      loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        // Swap root (largest element) with the last element of the current heap
        int temp = arr[0];
        arr[0] = arr[size - 1 - i];
        arr[size - 1 - i] = temp;

        // Heapify down the reduced heap (excluding the already extracted largest elements)
        heapify_down(arr, size - 1 - i, 0);
    }
}
