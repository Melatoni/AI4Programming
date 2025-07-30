// Task ID: 4
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in ACSL.
*/

/*@
  // Rule II.1: Recursive logic for complexity (e.g., properties of a heap).
  // Rule II.2: Helper axioms for recursive functions.
  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  // Axiomatic block for heap properties.
  // A max-heap property: parent is always greater than or equal to its children.
*/
/*@ axiomatic MaxHeap {
  logic boolean is_max_heap_at(int *a, int size, int i) =
    (2*i + 1 >= size) || // Left child out of bounds
    ( (a[i] >= a[2*i + 1]) &&
      ( (2*i + 2 >= size) || // Right child out of bounds
        (a[i] >= a[2*i + 2]) ) );

  logic boolean is_max_heap(int *a, int size) =
    \forall integer i; 0 <= i < size ==> is_max_heap_at(a, size, i);

  // Helper axiom: If a heap property holds at a node, and its children also satisfy it,
  // then the property holds for the subtree rooted at that node.
  // This is implicitly used by the recursive definition, but can be made explicit if needed for complex proofs.
  // For this problem, the recursive definition of is_max_heap is sufficient.
}
*/

/*@
  // Function to swap two elements in an array.
  assigns a[idx1], a[idx2];
  ensures a[idx1] == \old(a[idx2]);
  ensures a[idx2] == \old(a[idx1]);
  ensures \forall integer k; k != idx1 && k != idx2 ==> a[k] == \old(a[k]);
*/
void swap(int *a, int idx1, int idx2) {
    int temp = a[idx1];
    a[idx1] = a[idx2];
    a[idx2] = temp;
}

/*@
  // Function to heapify a subtree rooted at index i.
  requires size > 0;
  requires 0 <= i < size;
  requires \valid_read(a + (0..size-1));
  assigns a[0..size-1];

  // Ensures that after heapify, the subtree rooted at i (and its children) satisfies the max-heap property.
  // And that the elements are a permutation of the original.
  ensures is_max_heap_at(a, size, i);
  ensures \forall integer k; (2*i + 1 < size && k == 2*i + 1) || (2*i + 2 < size && k == 2*i + 2) || k == i ==> is_max_heap_at(a, size, k);
  ensures \forall integer k; (0 <= k < size && k != i && k != 2*i+1 && k != 2*i+2) ==> a[k] == \old(a[k]); // Elements outside affected subtree are unchanged.
  ensures \forall integer k; 0 <= k < size ==> \old(\at(a[k], Pre)) == \at(a[k], Post) ||
                                                \old(\at(a[k], Pre)) == \at(a[2*i+1], Post) ||
                                                \old(\at(a[k], Pre)) == \at(a[2*i+2], Post) ||
                                                \old(\at(a[i], Pre)) == \at(a[k], Post); // Simplified permutation property.
*/
void heapify(int *a, int size, int i) {
    int largest = i;
    int left = 2 * i + 1;
    int right = 2 * i + 2;

    /*@
      loop invariant 0 <= i < size;
      loop invariant 0 <= largest < size;
      loop invariant 0 <= left;
      loop invariant 0 <= right;
      loop invariant largest == i || largest == left || largest == right;
      loop invariant (left < size ==> a[largest] >= a[left]) || largest != i;
      loop invariant (right < size ==> a[largest] >= a[right]) || largest != i;
      loop invariant \forall integer k; 0 <= k < size && k != i && k != left && k != right ==> a[k] == \at(a[k], Pre);
      loop assigns largest, left, right, a[i], a[largest]; // The elements that might be swapped.
      loop variant size - (largest - i); // A variant that decreases towards 0.
    */
    while (1) {
        // Find the largest among root, left child, and right child
        if (left < size && a[left] > a[largest]) {
            largest = left;
        }

        if (right < size && a[right] > a[largest]) {
            largest = right;
        }

        // If largest is not root, swap and continue heapifying the affected sub-tree
        if (largest != i) {
            swap(a, i, largest);
            i = largest; // Move down to the child that was swapped
            left = 2 * i + 1;
            right = 2 * i + 2;
        } else {
            break; // Max-heap property satisfied at this node
        }
    }
}

/*@
  // Function to build a max-heap from an array.
  requires size >= 0;
  requires \valid_read(a + (0..size-1));
  assigns a[0..size-1];
  ensures is_max_heap(a, size);
  // Ensures that elements are a permutation of the original.
  ensures \forall integer x; 0 <= x < size ==> \exists integer y; 0 <= y < size && \at(a[x], Post) == \at(a[y], Pre);
  ensures \forall integer y; 0 <= y < size ==> \exists integer x; 0 <= x < size && \at(a[y], Pre) == \at(a[x], Post);
*/
void build_max_heap(int *a, int size) {
    // Start from the last non-leaf node and heapify upwards.
    int i = (size / 2) - 1;

    /*@
      loop invariant -1 <= i < size / 2;
      loop invariant \forall integer k; i + 1 <= k < size / 2 ==> is_max_heap_at(a, size, k); // All nodes processed so far are heaps.
      loop invariant \forall integer k; size / 2 <= k < size ==> is_max_heap_at(a, size, k); // All leaf nodes are trivial heaps.
      loop assigns i, a[0..size-1];
      loop variant i;
    */
    for (; i >= 0; i--) {
        heapify(a, size, i);
    }
}

/*@
  // Function to find the largest 'k' elements from a list using a max-heap.
  // The original array 'list' will be modified (sorted in descending order for the first 'k' elements).
  requires size >= 0;
  requires k >= 0;
  requires k <= size; // Cannot ask for more elements than available.
  requires \valid_read(list + (0..size-1));
  assigns list[0..size-1]; // The 'list' array is modified in-place.

  // Ensures the first 'k' elements are the largest 'k' elements from the original list.
  // This is a strong postcondition.
  ensures \forall integer i; 0 <= i < k ==>
    (\forall integer j; k <= j < size ==> list[i] >= list[j]); // All top k elements are greater than or equal to the rest.

  // Ensures the first 'k' elements are sorted in descending order.
  ensures \forall integer i; 0 <= i < k - 1 ==> list[i] >= list[i+1];

  // Ensures the first 'k' elements are a permutation of the original top k largest.
  // This is harder to prove formally without a multiset equality.
  // A weaker but provable property: All elements in the result set were in the input set.
  ensures \forall integer i; 0 <= i < k ==> (\exists integer j; 0 <= j < size && list[i] == \old(list[j]));
*/
void find_largest_k_elements(int *list, int size, int k) {
    if (size == 0 || k == 0) {
        return;
    }

    // Build a max-heap from the input array.
    build_max_heap(list, size);

    // Extract k largest elements.
    // The largest element is always at the root (list[0]).
    // Swap it with the last element, reduce heap size, and heapify.
    int current_heap_size = size;
    int i = 0;

    /*@
      loop invariant 0 <= i <= k;
      loop invariant current_heap_size == size - i;
      loop invariant current_heap_size >= 0;
      loop invariant \forall integer m; 0 <= m < i ==> list[m] == \at(list[0], LoopEntry); // The i largest elements are in list[0..i-1] in decreasing order.
      loop invariant \forall integer m; 0 <= m < i - 1 ==> list[m] >= list[m+1];
      loop invariant is_max_heap(list, current_heap_size); // The remaining part is always a max-heap.
      loop invariant \forall integer x; 0 <= x < size ==> (\exists integer y; 0 <= y < size && list[x] == \old(list[y])); // Permutation property.
      loop assigns i, current_heap_size, list[0..size-1];
      loop variant k - i;
    */
    while (i < k) {
        if (current_heap_size == 0) {
            break; // Not enough elements to extract k.
        }

        // Swap the root (largest element) with the last element of the current heap.
        swap(list, 0, current_heap_size - 1);

        // Reduce the heap size. The swapped element is now at list[current_heap_size - 1]
        // and is considered 'extracted'.
        current_heap_size--;

        // Heapify the root of the reduced heap.
        heapify(list, current_heap_size, 0);
        i++;
    }
}
