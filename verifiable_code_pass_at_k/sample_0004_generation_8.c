// Task ID: 4
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  axiomatic MaxHeap {
    logic integer get_parent_idx(integer i) = (i - 1) / 2;
    logic integer get_left_child_idx(integer i) = 2 * i + 1;
    logic integer get_right_child_idx(integer i) = 2 * i + 2;

    // A predicate to check if a subarray is a max heap.
    // The heap property states that for any node i, its value is greater than or equal to its children's values.
    predicate is_max_heap{L}(int* arr, integer len) =
      \forall integer i;
        0 <= i < len && get_left_child_idx(i) < len ==> arr[i] >= arr[get_left_child_idx(i)] &&
        0 <= i < len && get_right_child_idx(i) < len ==> arr[i] >= arr[get_right_child_idx(i)];

    // Helper axiom: if a heap is empty or has one element, it's a max heap.
    axiom empty_or_single_is_heap:
      \forall int* arr, integer len;
        len <= 1 ==> is_max_heap(arr, len);

    // Helper axiom: if a heap is valid, its children's sub-heaps are also valid.
    axiom heap_children_valid:
      \forall int* arr, integer len, integer i;
        is_max_heap(arr, len) && get_left_child_idx(i) < len ==> is_max_heap(arr + get_left_child_idx(i), len - get_left_child_idx(i));
        is_max_heap(arr, len) && get_right_child_idx(i) < len ==> is_max_heap(arr + get_right_child_idx(i), len - get_right_child_idx(i));
  }
*/

/*@
  requires \valid_read(arr + (0..len-1));
  requires len >= 0;
  requires idx >= 0 && idx < len;
  // Rule II.5: Prevent RTE for children indices.
  requires get_left_child_idx(idx) <= 2147483646; // INT_MAX - 1 for 2*idx+1
  requires get_right_child_idx(idx) <= 2147483645; // INT_MAX - 2 for 2*idx+2

  assigns arr[idx], arr[get_left_child_idx(idx)], arr[get_right_child_idx(idx)];
  assigns arr[\old(idx)], arr[\old(get_left_child_idx(idx))], arr[\old(get_right_child_idx(idx))];
  assigns arr[0..len-1]; // Potentially modifies any element that gets swapped

  // Ensures that after heapify, the element at idx is greater than or equal to its children,
  // and the subtrees rooted at its children are also max heaps.
  ensures is_max_heap(arr, len);
  ensures \forall integer k; 0 <= k < len ==> \old(arr[k]) == arr[k] || k == idx || k == get_left_child_idx(idx) || k == get_right_child_idx(idx) || k == \old(idx) || k == \old(get_left_child_idx(idx)) || k == \old(get_right_child_idx(idx));
*/
void heapify(int* arr, int len, int idx) {
    int largest = idx;
    int left = 2 * idx + 1;
    int right = 2 * idx + 2;

    /*@
      loop invariant 0 <= largest < len;
      loop invariant 0 <= idx < len;
      loop invariant (left == 2*idx + 1) && (right == 2*idx + 2);
      loop invariant \forall integer k; 0 <= k < len && k != idx && k != left && k != right ==> arr[k] == \at(arr[k], LoopEntry);
      loop invariant arr[largest] >= arr[idx]; // If largest changed, it means it's greater than current idx
      loop invariant is_max_heap(arr, len); // This is strong, but necessary for the postcondition.
                                           // The WP prover might struggle with this without more specific loop invariants
                                           // about the partially heapified state.
                                           // A more relaxed invariant would be that the elements not involved in the current
                                           // subtree rooted at idx maintain their heap property.

      loop variant (largest == idx ? 0 : 1); // Variant to show termination (at most one swap that triggers recursion)
    */
    while (1) {
        /*@
          assert 0 <= largest < len;
          assert 0 <= idx < len;
          assert (left == 2*idx + 1) && (right == 2*idx + 2);
        */
        if (left < len && arr[left] > arr[largest]) {
            largest = left;
        }

        if (right < len && arr[right] > arr[largest]) {
            largest = right;
        }

        if (largest != idx) {
            int temp = arr[idx];
            arr[idx] = arr[largest];
            arr[largest] = temp;

            idx = largest;
            left = 2 * idx + 1;
            right = 2 * idx + 2;
        } else {
            break;
        }
    }
}

/*@
  requires \valid_read(arr + (0..len-1));
  requires len >= 0;
  assigns arr[0..len-1];
  ensures is_max_heap(arr, len);
  ensures \forall integer i; 0 <= i < len ==> \exists integer j; 0 <= j < len && arr[i] == \old(arr[j]); // Permutation
*/
void build_max_heap(int* arr, int len) {
    /*@
      loop invariant -1 <= i < len;
      loop invariant \forall integer k; i < k < len ==> is_max_heap(arr + k, len - k); // Subtrees from i+1 to len-1 are heaps.
      loop invariant \forall integer k; 0 <= k < len ==> \exists integer j; 0 <= j < len && arr[k] == \at(arr[j], LoopEntry); // Permutation
      loop assigns i, arr[0..len-1];
      loop variant i;
    */
    for (int i = len / 2 - 1; i >= 0; i--) {
        heapify(arr, len, i);
    }
}

/*@
  requires \valid_read(arr + (0..len-1));
  requires \valid_write(result_arr + (0..k-1));
  requires len >= 0;
  requires k >= 0;
  requires k <= len; // Cannot find more largest elements than available in the array.

  assigns arr[0..len-1];
  assigns result_arr[0..k-1];

  // Ensures that result_arr contains the k largest elements from the original arr.
  // This is a complex postcondition. We need to define what "k largest" means.
  // It means that for any element in result_arr, it is greater than or equal to any element
  // in the remaining (len-k) elements of arr.
  // And all elements in result_arr must have been present in the original array.
  ensures \forall integer i; 0 <= i < k ==> \exists integer j; 0 <= j < \old(len) && result_arr[i] == \old(arr[j]); // Elements are from original array
  ensures \forall integer i; 0 <= i < k ==>
            \forall integer l; 0 <= l < len - k ==> result_arr[i] >= arr[l]; // All k largest are indeed larger than remaining
*/
void find_k_largest(int* arr, int len, int k, int* result_arr) {
    build_max_heap(arr, len);

    /*@
      loop invariant 0 <= i <= k;
      loop invariant i <= len;
      loop invariant \forall integer j; 0 <= j < i ==> \exists integer l; 0 <= l < \old(len) && result_arr[j] == \old(arr[l]); // Elements collected are from original array
      loop invariant \forall integer j; 0 <= j < i ==> \forall integer m; i <= m < len ==> result_arr[j] >= arr[m]; // Collected elements are larger than remaining
      loop invariant is_max_heap(arr, len - i); // The remaining part of arr is still a max heap
      loop invariant \forall integer x; 0 <= x < i ==> \forall integer y; x < i ==> result_arr[x] >= result_arr[y]; // result_arr is sorted decreasingly
      loop assigns i, arr[0..len-1], result_arr[0..k-1];
      loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        if (len - i <= 0) { // Safety check if k is larger than remaining heap size
            break;
        }

        result_arr[i] = arr[0]; // The largest element is always at the root

        // Swap root with the last element of the current heap
        int temp = arr[0];
        arr[0] = arr[len - 1 - i];
        arr[len - 1 - i] = temp;

        // Heapify the reduced heap (excluding the extracted largest element)
        heapify(arr, len - 1 - i, 0);
    }
}
