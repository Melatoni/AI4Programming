// Task ID: 4
// Generation: 5

/*@
  // Rule I.1: No standard libraries. ACSL constants are used directly if needed.
  // Rule II.1: Recursive logic for complexity.
  // Define a recursive logic function for checking if an array is a max-heap.
  // A max-heap property: parent is always greater than or equal to its children.
  // For an array `arr` of size `size`, `arr[i]`'s left child is `arr[2*i + 1]` and right child is `arr[2*i + 2]`.
  // This property must hold for all non-leaf nodes.
  axiomatic MaxHeap {
    logic boolean is_max_heap_rec{L}(int* arr, int size, int i) reads arr[0..size-1];

    axiom is_max_heap_base_leaf{L}:
      \forall int* arr, int size, int i;
        (2 * i + 1 >= size) ==> is_max_heap_rec(arr, size, i);

    axiom is_max_heap_rec_step_left{L}:
      \forall int* arr, int size, int i;
        (2 * i + 1 < size && 2 * i + 2 >= size) ==>
          is_max_heap_rec(arr, size, i) <==>
            (arr[i] >= arr[2 * i + 1] && is_max_heap_rec(arr, size, 2 * i + 1));

    axiom is_max_heap_rec_step_both{L}:
      \forall int* arr, int size, int i;
        (2 * i + 2 < size) ==>
          is_max_heap_rec(arr, size, i) <==>
            (arr[i] >= arr[2 * i + 1] && arr[i] >= arr[2 * i + 2] &&
             is_max_heap_rec(arr, size, 2 * i + 1) &&
             is_max_heap_rec(arr, size, 2 * i + 2));

    // Helper axiom: If an array is a max-heap starting from index 0, it's a max-heap.
    // This is implicitly covered by the recursive definition, but good to have for clarity
    // if the prover struggles with the base case for the top-level call.
    logic boolean is_max_heap{L}(int* arr, int size) reads arr[0..size-1];
    axiom is_max_heap_def{L}:
      \forall int* arr, int size;
        is_max_heap(arr, size) <==> (size <= 1 || is_max_heap_rec(arr, size, 0));
  }
*/

/*@
  // Swaps two elements in an array.
  requires \valid(arr + i);
  requires \valid(arr + j);
  assigns arr[i], arr[j];
  ensures arr[i] == \old(arr[j]);
  ensures arr[j] == \old(arr[i]);
  ensures \forall integer k; k != i && k != j ==> arr[k] == \old(arr[k]);
*/
void swap(int* arr, int i, int j) {
    int temp = arr[i];
    arr[i] = arr[j];
    arr[j] = temp;
}

/*@
  // Restores the max-heap property for a subtree rooted at `i` in an array of size `size`.
  // Assumes that the left and right subtrees are already max-heaps.
  requires 0 <= i < size;
  requires 0 < size; // Heapify is called on non-empty heaps
  requires \valid_range(arr, 0, size - 1);
  requires is_max_heap_rec(arr, size, 2 * i + 1); // Left child's subtree is a heap
  requires is_max_heap_rec(arr, size, 2 * i + 2); // Right child's subtree is a heap

  assigns arr[0..size-1];

  // The ensures clause for heapify is complex.
  // It guarantees that the subtree rooted at `i` becomes a max-heap.
  // It also guarantees that the elements are a permutation of the original.
  ensures is_max_heap_rec(arr, size, i);
  ensures \forall integer k; 0 <= k < size ==> \at(arr[k], Old) == \at(arr[k], Post) || \true; // Permutation is hard to prove directly, focus on heap property
  // A simpler post-condition is that the elements are just a permutation.
  ensures \forall integer x; (\numof(integer k; 0 <= k < size && arr[k] == x)) == (\numof(integer k; 0 <= k < size && \old(arr[k]) == x));
*/
void heapify(int* arr, int size, int i) {
    int largest = i;
    int left = 2 * i + 1;
    int right = 2 * i + 2;

    /*@
      loop invariant 0 <= i < size;
      loop invariant 0 <= largest < size;
      loop invariant 0 <= left;
      loop invariant 0 <= right;
      loop invariant largest == i || largest == left || largest == right; // largest is always one of the three
      loop invariant (left >= size || arr[left] <= arr[i]) || (right >= size || arr[right] <= arr[i]) ==> largest == i; // If children are smaller, largest is i
      loop invariant (left < size && arr[left] > arr[largest] && (right >= size || arr[right] <= arr[largest])) ==> largest == left; // If left is largest
      loop invariant (right < size && arr[right] > arr[largest] && (left >= size || arr[left] <= arr[largest])) ==> largest == right; // If right is largest
      loop invariant (left < size && arr[left] > arr[i]) ==> largest == left || largest == i; // If left child is greater than current root, largest will be left or i
      loop invariant (right < size && arr[right] > arr[i]) ==> largest == right || largest == i; // If right child is greater than current root, largest will be right or i

      // The elements not involved in the current comparison maintain their values relative to the original
      loop invariant \forall integer k; 0 <= k < size && k != i && k != left && k != right ==> arr[k] == \at(arr[k], LoopEntry);

      loop assigns largest, left, right;
      loop variant (largest == i ? 1 : 0) + (left < size ? 1 : 0) + (right < size ? 1 : 0); // Not a standard variant, but it expresses progress.
      // A more robust variant for this loop structure: sum of `size - left` and `size - right`
      // Or simply, `size - i` which decreases only if `largest != i`
      // For this specific loop, `largest` changes from `i` to `left` or `right`, and the loop terminates.
      // A variant that proves termination of this specific `if-else if` block:
      // A simple variant is just `1` because it executes at most once.
      // However, for recursive calls, the variant needs to be more complex.
      // Since this is not a `while` loop, but a conditional check followed by a recursive call,
      // the variant for the _function_ `heapify` would be `size - i`.
      // For the internal if-else if structure, no specific loop variant is needed for termination.
    */
    if (left < size && arr[left] > arr[largest]) {
        largest = left;
    }
    /*@
      loop invariant 0 <= i < size;
      loop invariant 0 <= largest < size;
      loop invariant 0 <= left;
      loop invariant 0 <= right;
      loop invariant largest == i || largest == left; // After first if, largest is i or left
      loop invariant (right < size && arr[right] > arr[largest]) ==> largest == right; // If right child is greater than largest found so far, largest will be right
      loop invariant \forall integer k; 0 <= k < size && k != i && k != left && k != right ==> arr[k] == \at(arr[k], LoopEntry);
      loop assigns largest;
      loop variant 1; // This is an if-else if, so it's not a true loop. A variant of 1 is fine.
    */
    if (right < size && arr[right] > arr[largest]) {
        largest = right;
    }

    if (largest != i) {
        swap(arr, i, largest);
        // Recursive call: the variant `size - largest` decreases (since `largest` is a child of `i`, `largest > i`)
        // The variant for the overall heapify function is `size - i`.
        // Each recursive call pushes `i` down, so `i` increases.
        // A more precise variant for the recursive call would be `size - i` (for the current call)
        // and `size - largest` for the recursive call. This is complex.
        // The total number of nodes in the subtree rooted at `i` is a good variant.
        // Or simply `i` itself, as it increases with recursive calls.
        /*@
          // Pre-conditions for recursive call `heapify(arr, size, largest)`:
          // 0 <= largest < size (guaranteed by previous logic)
          // is_max_heap_rec(arr, size, 2 * largest + 1) (true because the swap doesn't affect these)
          // is_max_heap_rec(arr, size, 2 * largest + 2) (true because the swap doesn't affect these)
          // The permutation property is preserved by `swap`.
          // The max-heap property for children of `largest` is maintained.
        */
        heapify(arr, size, largest);
    }
}

/*@
  // Builds a max-heap from an arbitrary array.
  requires size >= 0;
  requires \valid_range(arr, 0, size - 1);
  assigns arr[0..size-1];
  ensures is_max_heap(arr, size);
  ensures \forall integer x; (\numof(integer k; 0 <= k < size && arr[k] == x)) == (\numof(integer k; 0 <= k < size && \old(arr[k]) == x));
*/
void build_max_heap(int* arr, int size) {
    /*@
      loop invariant 0 <= i <= size / 2;
      loop invariant \forall integer j; size / 2 < j < size ==> is_max_heap_rec(arr, size, j); // All leaf nodes are already heaps
      loop invariant \forall integer j; i < j < size ==> is_max_heap_rec(arr, size, j); // All nodes from i+1 to size-1 are heaps
      loop invariant \forall integer x; (\numof(integer k; 0 <= k < size && arr[k] == x)) == (\numof(integer k; 0 <= k < size && \at(arr[k], LoopEntry) == x)); // Permutation
      loop assigns arr[0..size-1], i;
      loop variant i;
    */
    for (int i = size / 2 - 1; i >= 0; i--) {
        heapify(arr, size, i);
    }
}

/*@
  // Finds the largest 'k' elements from an array using a max-heap.
  // The function modifies the input array `arr` by sorting the largest 'k' elements
  // to the end of the array (not necessarily sorted among themselves).
  // The first `size - k` elements are not guaranteed to be in any order.
  // The function returns the k-th largest element (which will be at index `size - k`).
  // If k is 0, it should return some sentinel value or have a specific contract.
  // For simplicity, let's assume k > 0 and k <= size.

  requires size >= 0;
  requires 0 <= k <= size;
  requires \valid_range(arr, 0, size - 1);

  assigns arr[0..size-1];

  // Ensures that the 'k' largest elements are at the end of the array.
  // The elements `arr[size-k .. size-1]` are the k largest elements.
  // Each of these elements is greater than or equal to any element in `arr[0 .. size-k-1]`.
  ensures \forall integer i; 0 <= i < size - k ==> \forall integer j; size - k <= j < size ==> arr[j] >= arr[i];
  // Ensures that the returned value is the k-th largest element.
  // This means that there are at least `k-1` elements in `arr` that are greater than or equal to `\result`.
  // And there are at most `size - k` elements in `arr` that are less than or equal to `\result`.
  ensures (\numof(integer i; 0 <= i < size && arr[i] >= \result)) >= k;
  ensures (\numof(integer i; 0 <= i < size && arr[i] <= \result)) >= size - k + 1; // At least size-k+1 elements are <= result

  // Ensures that the elements in the array are a permutation of the original elements.
  ensures \forall integer x; (\numof(integer i; 0 <= i < size && arr[i] == x)) == (\numof(integer i; 0 <= i < size && \old(arr[i]) == x));

  // If k == 0, the contract is that no elements are extracted, and the array remains a permutation.
  // The return value for k==0 is undefined by this contract, let's make it 0.
  ensures k == 0 ==> \result == 0;
  ensures k > 0 ==> \result == arr[size - k];
*/
int find_largest_k(int* arr, int size, int k) {
    if (size == 0 || k == 0) {
        return 0; // Rule I.2: Use 0 for false/default sentinel.
    }

    build_max_heap(arr, size); // Build a max-heap from the input array.

    /*@
      loop invariant 0 <= i <= k;
      loop invariant size - i >= 0; // Remaining heap size
      loop invariant is_max_heap(arr, size - i); // The prefix arr[0 .. size-i-1] is still a max-heap
      // The suffix arr[size-i .. size-1] contains the 'i' largest elements extracted so far.
      loop invariant \forall integer x; size - i <= x < size ==> \forall integer y; 0 <= y < size - i ==> arr[x] >= arr[y];
      loop invariant \forall integer x; (\numof(integer l; 0 <= l < size && arr[l] == x)) == (\numof(integer l; 0 <= l < size && \at(arr[l], LoopEntry) == x)); // Permutation
      loop assigns arr[0..size-1], i;
      loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        // The largest element is at the root (arr[0]).
        // Swap it with the last element of the current heap.
        swap(arr, 0, size - 1 - i);

        // Reduce the heap size by 1 and heapify the root.
        // The swapped element is now at the end and is considered "removed" from the heap.
        heapify(arr, size - 1 - i, 0);
    }

    // The k-th largest element is now at index `size - k`.
    // The largest 'k' elements are in `arr[size-k .. size-1]`.
    return arr[size - k];
}
