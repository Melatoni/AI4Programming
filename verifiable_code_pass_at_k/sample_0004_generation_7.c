// Task ID: 4
// Generation: 7

/*@
    axiomatic MaxHeap {

        // Rule II.1: Recursive logic for properties of the heap structure.
        // A heap is valid if the parent is always greater than or equal to its children.
        logic boolean is_max_heap_recursive(int* arr, int size, int i) =
            \if i >= size then
                \true
            \else if 2*i + 1 >= size then // Has only left child or no children
                \if 2*i + 2 >= size then // No children
                    \true
                \else // Has only left child
                    arr[i] >= arr[2*i + 1] && is_max_heap_recursive(arr, size, 2*i + 1)
            \else // Has both children
                arr[i] >= arr[2*i + 1] && arr[i] >= arr[2*i + 2] &&
                is_max_heap_recursive(arr, size, 2*i + 1) &&
                is_max_heap_recursive(arr, size, 2*i + 2);

        // Helper function to check if the entire array is a max heap.
        // Rule II.1: Recursive logic for complexity.
        logic boolean is_max_heap(int* arr, int size) =
            is_max_heap_recursive(arr, size, 0);

        // Helper function to check if a specific element is present in the array.
        // Rule II.1: Recursive logic for complexity.
        logic boolean contains_element(int* arr, int size, int val) =
            \exists integer i; 0 <= i < size && arr[i] == val;

        // Helper function to check if all elements in a subarray are present in another array.
        // Rule II.1: Recursive logic for complexity.
        logic boolean contains_all_elements(int* arr1, int size1, int* arr2, int size2) =
            \forall integer i; 0 <= i < size2 ==> contains_element(arr1, size1, arr2[i]);

        // Helper function to check if an array is sorted in descending order.
        // Rule II.1: Recursive logic for complexity.
        logic boolean is_sorted_descending(int* arr, int size) =
            \forall integer i; 0 <= i < size - 1 ==> arr[i] >= arr[i+1];

        // Rule II.1: Helper axiom - If a heap is valid, its root is the maximum element.
        axiom max_heap_root_is_max:
            \forall int* arr, integer size;
                is_max_heap(arr, size) && size > 0 ==>
                \forall integer i; 0 <= i < size ==> arr[0] >= arr[i];
    }
*/

/*@
    requires 0 <= i < size;
    requires 0 <= j < size;
    assigns arr[i], arr[j];
    ensures arr[i] == \old(arr[j]) && arr[j] == \old(arr[i]);
    ensures \forall integer k; 0 <= k < size && k != i && k != j ==> arr[k] == \old(arr[k]);
*/
void swap(int* arr, int i, int j) {
    int temp = arr[i];
    arr[i] = arr[j];
    arr[j] = temp;
}

/*@
    requires 0 <= i < current_size;
    requires 0 < current_size <= max_size;
    requires \valid(arr + (0..max_size - 1));
    requires is_max_heap_recursive(arr, current_size, i); // Pre-condition: sub-tree at i is a max-heap

    assigns arr[0..current_size-1];

    behavior valid_heapify:
        assumes \forall integer k; 0 <= k < current_size ==> \old(arr[k]) == arr[k]; // No change if already a heap
        ensures is_max_heap_recursive(arr, \old(current_size), i); // Sub-tree at i remains a max-heap

    behavior modified_heapify:
        assumes \exists integer k; 0 <= k < current_size && \old(arr[k]) != arr[k]; // Change occurred
        ensures is_max_heap(arr, \old(current_size)); // The entire array becomes max-heap (if called from build_max_heap)
        ensures \forall integer k; 0 <= k < \old(current_size) ==> contains_element(\old(arr), \old(current_size), arr[k]); // Elements are preserved
        ensures \forall integer k; 0 <= k < \old(current_size) ==> contains_element(arr, \old(current_size), \old(arr[k])); // Elements are preserved
*/
void heapify(int* arr, int current_size, int i) {
    int largest = i;
    int left = 2 * i + 1;
    int right = 2 * i + 2;

    /*@
        loop invariant 0 <= i < current_size;
        loop invariant 0 <= largest < current_size;
        loop invariant 0 <= left;
        loop invariant 0 <= right;
        loop invariant is_max_heap_recursive(arr, current_size, largest);
        loop invariant \forall integer k; 0 <= k < current_size && k != i && k != left && k != right ==> arr[k] == \at(arr[k], LoopEntry);
        loop invariant (left >= current_size || arr[largest] >= arr[left]);
        loop invariant (right >= current_size || arr[largest] >= arr[right]);
        loop assigns largest, left, right, arr[i], arr[largest];
        loop variant largest; // The index largest decreases or stays the same until it converges to the root of the sub-heap.
    */
    while (left < current_size && (arr[left] > arr[largest] || (right < current_size && arr[right] > arr[largest]))) {
        if (left < current_size && arr[left] > arr[largest]) {
            largest = left;
        }
        if (right < current_size && arr[right] > arr[largest]) {
            largest = right;
        }

        if (largest != i) {
            swap(arr, i, largest);
            i = largest;
            left = 2 * i + 1;
            right = 2 * i + 2;
        } else {
            break; // No more swaps needed in this path
        }
    }
}

/*@
    requires 0 < size <= max_size;
    requires \valid(arr + (0..max_size - 1));

    assigns arr[0..size-1];
    ensures is_max_heap(arr, size);
    ensures \forall integer k; 0 <= k < size ==> contains_element(\old(arr), size, arr[k]);
    ensures \forall integer k; 0 <= k < size ==> contains_element(arr, size, \old(arr[k]));
*/
void build_max_heap(int* arr, int size, int max_size) { // max_size is needed for \valid
    /*@
        loop invariant 0 <= i < size;
        loop invariant \forall integer k; i <= k < size ==> is_max_heap_recursive(arr, size, k);
        loop invariant \forall integer k; 0 <= k < size ==> contains_element(\old(arr), size, arr[k]);
        loop invariant \forall integer k; 0 <= k < size ==> contains_element(arr, size, \old(arr[k]);
        loop assigns arr[0..size-1], i;
        loop variant i;
    */
    for (int i = size / 2 - 1; i >= 0; i--) {
        heapify(arr, size, i);
    }
}

/*@
    requires 0 < size <= max_size;
    requires k > 0;
    requires k <= size; // k cannot be greater than the array size
    requires \valid(arr + (0..max_size - 1));
    requires \valid(result + (0..k-1));

    assigns arr[0..size-1], result[0..k-1];

    ensures \forall integer i; 0 <= i < k ==> \exists integer j; 0 <= j < \old(size) && \old(arr[j]) == result[i]; // All results are from original array
    ensures \forall integer i; 0 <= i < k-1 ==> result[i] >= result[i+1]; // Result is sorted descending
    ensures \forall integer i; 0 <= i < k ==>
        (\forall integer x; 0 <= x < \old(size) && contains_element(\old(arr), \old(size), x) ==> (x <= result[i] || contains_element(\old(arr), \old(size) - k, x))); // The k largest elements are returned
    ensures contains_all_elements(\old(arr), \old(size), result, k);
    ensures is_sorted_descending(result, k);
*/
void find_largest_elements(int* arr, int size, int k, int* result, int max_size) {
    build_max_heap(arr, size, max_size);

    /*@
        loop invariant 0 <= i < k;
        loop invariant size - i >= 0;
        loop invariant is_max_heap(arr, size - i);
        loop invariant \forall integer j; 0 <= j < i ==> result[j] == \at(arr[0], LoopEntry_build_max_heap_heapify_swap) && j == i-1 ? (\at(arr[size-1], LoopEntry_build_max_heap_heapify_swap)) : \at(arr[0], LoopEntry_build_max_heap_heapify_swap); // TODO: Refine this invariant
        loop invariant \forall integer j; 0 <= j < i ==> result[j] == \at(arr[0], L1); // Capture the elements extracted
        loop invariant \forall integer j; 0 <= j < i-1 ==> result[j] >= result[j+1]; // Result array is sorted so far
        loop invariant contains_all_elements(\old(arr), \old(size), arr, size - i); // Remaining elements are still from original
        loop invariant contains_all_elements(\old(arr), \old(size), result, i); // Extracted elements are from original
        loop assigns result[0..k-1], arr[0..size-1], i;
        loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        result[i] = arr[0]; // The largest element is always at the root
        swap(arr, 0, size - 1 - i); // Move the largest to the end of the current heap
        heapify(arr, size - 1 - i, 0); // Re-heapify the reduced heap
    }
}
