// Task ID: 4
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: int for booleans.
  // Rule I.3: Array pointer decay.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic MaxHeap {
  @   logic integer parent(integer i) = (i - 1) / 2;
  @   logic integer left_child(integer i) = 2 * i + 1;
  @   logic integer right_child(integer i) = 2 * i + 2;

  @   // Rule II.1: Recursive logic for complexity.
  @   // Predicate to check if a subtree rooted at `idx` is a max-heap.
  @   // Assumes that children are within array bounds.
  @   predicate is_max_heap_root{L}(int* arr, integer len, integer idx) =
  @     (left_child(idx) >= len || arr[idx] >= arr[left_child(idx)]) &&
  @     (right_child(idx) >= len || arr[idx] >= arr[right_child(idx)]);

  @   // Predicate to check if an array segment is a max-heap.
  @   // Rule II.1: Recursive logic for complexity.
  @   predicate is_max_heap{L}(int* arr, integer len) =
  @     \forall integer i; 0 <= i < len ==> is_max_heap_root{L}(arr, len, i);

  @   // Helper axiom: if a segment is a max-heap, then any smaller segment within it
  @   // starting from 0 is also a max-heap.
  @   // Rule II.2: CRITICAL - Helper Axioms.
  @   axiom is_max_heap_subsegment{L}:
  @     \forall int* arr, integer len, integer sub_len;
  @       0 <= sub_len <= len && is_max_heap{L}(arr, len) ==> is_max_heap{L}(arr, sub_len);

  @   // Helper axiom: if an array is a max-heap, then the root is the maximum element.
  @   // Rule II.2: CRITICAL - Helper Axioms.
  @   axiom max_heap_root_is_max{L}:
  @     \forall int* arr, integer len;
  @       len > 0 && is_max_heap{L}(arr, len) ==> \forall integer i; 0 <= i < len ==> arr[0] >= arr[i];
  @ }
*/

/*@
  requires 0 <= i < len;
  requires 0 <= j < len;
  assigns arr[i], arr[j];
  ensures arr[i] == \old(arr[j]) && arr[j] == \old(arr[i]);
  ensures \forall integer k; 0 <= k < len && k != i && k != j ==> arr[k] == \old(arr[k]);
*/
void swap(int* arr, int i, int j, int len) {
  int temp = arr[i];
  arr[i] = arr[j];
  arr[j] = temp;
}

/*@
  requires len >= 0;
  requires 0 <= idx < len;
  requires \valid_range(arr, 0, len - 1);
  assigns arr[idx], arr[left_child(idx)], arr[right_child(idx)];
  // Ensures that after heapify, the subtree rooted at idx is a max-heap.
  // Rule II.3: ensures clause for boolean-like functions.
  ensures is_max_heap_root(arr, len, idx);
  // Ensures that elements not involved in heapify are unchanged.
  ensures \forall integer k; 0 <= k < len && k != idx && k != left_child(idx) && k != right_child(idx) ==> arr[k] == \old(arr[k]);
*/
void max_heapify(int* arr, int len, int idx) {
  int largest = idx;
  int left = left_child(idx);
  int right = right_child(idx);

  /*@
    loop invariant 0 <= idx < len;
    loop invariant 0 <= largest < len;
    loop invariant 0 <= left < len + 2; // Can be len or len+1 if idx is close to end
    loop invariant 0 <= right < len + 2; // Can be len or len+1 if idx is close to end
    loop invariant (left < len ==> largest == idx || arr[largest] >= arr[left]);
    loop invariant (right < len ==> largest == idx || arr[largest] >= arr[right]);
    loop invariant \forall integer k; 0 <= k < len && k != idx && k != left && k != right ==> arr[k] == \old(arr[k]);
    loop assigns largest, left, right, arr[idx], arr[left_child(idx)], arr[right_child(idx)];
    loop variant (largest == idx ? 1 : 0); // Loop terminates when largest is not idx, or when children are out of bounds.
  */
  while (1) { // This loop structure is common for heapify, it might run at most twice or three times
    int old_largest = largest;
    if (left < len && arr[left] > arr[largest]) {
      largest = left;
    }

    if (right < len && arr[right] > arr[largest]) {
      largest = right;
    }

    if (largest != idx) {
      swap(arr, idx, largest, len);
      idx = largest;
      left = left_child(idx);
      right = right_child(idx);
    } else {
      break;
    }
  }
}

/*@
  requires len >= 0;
  requires \valid_range(arr, 0, len - 1);
  assigns arr[0..len-1];
  ensures is_max_heap(arr, len);
*/
void build_max_heap(int* arr, int len) {
  /*@
    loop invariant -1 <= i < len;
    loop invariant \forall integer j; i < j < len ==> is_max_heap_root(arr, len, j);
    loop invariant is_max_heap(arr, (i+1 < len ? i + 1 : len)); // The segment from i+1 to len-1 is already heapified.
    loop assigns i, arr[0..len-1];
    loop variant i;
  */
  for (int i = len / 2 - 1; i >= 0; i--) {
    max_heapify(arr, len, i);
  }
}

/*@
  requires n >= 0;
  requires k >= 0;
  requires k <= n; // k must be <= n
  requires \valid_range(arr, 0, n - 1);
  assigns arr[0..n-1];
  // Ensures that the first k elements of the array are the k largest elements.
  // The order among the k largest elements is not guaranteed after this function.
  // The remaining n-k elements are the smallest.
  ensures \forall integer i; 0 <= i < k ==> (\forall integer j; k <= j < n ==> arr[i] >= arr[j]);
*/
void find_largest_k_elements(int* arr, int n, int k) {
  if (n == 0 || k == 0) {
    return;
  }

  build_max_heap(arr, n);

  /*@
    loop invariant 0 <= i <= k;
    loop invariant i <= n; // current size of heap
    loop invariant \forall integer l; 0 <= l < i ==> (\forall integer m; i <= m < n ==> arr[l] >= arr[m]); // Elements moved to the end are the largest so far.
    loop invariant is_max_heap(arr, n - i); // The remaining part of the array is still a max-heap.
    loop assigns i, arr[0..n-1];
    loop variant k - i;
  */
  for (int i = 0; i < k; i++) {
    if (n - i <= 0) break; // Should not happen if k <= n
    swap(arr, 0, n - 1 - i, n - i); // Move current max (root) to the end of the current heap segment
    max_heapify(arr, n - 1 - i, 0); // Heapify the reduced heap
  }
}
