// Task ID: 31
// Generation: 3

/*@ axiomatic Freq {
  @   logic integer count_occurrence{L}(int val, int* arr, int size);
  @
  @   axiom count_occurrence_empty{L}:
  @     \forall int val, int* arr; count_occurrence(val, arr, 0) == 0;
  @
  @   axiom count_occurrence_rec{L}:
  @     \forall int val, int* arr, int size;
  @       size > 0 ==> count_occurrence(val, arr, size) ==
  @         (if arr[size - 1] == val then 1 else 0) + count_occurrence(val, arr, size - 1);
  @ }
  @*/

/*@ axiomatic Heap {
  @   // Rule I.3: Array pointer decay must be handled.
  @   logic boolean is_heap{L}(int (*heap)[2], int size);
  @   logic boolean is_max_heap{L}(int (*heap)[2], int size);
  @   logic boolean is_min_heap{L}(int (*heap)[2], int size);
  @
  @   // A heap is empty or satisfies the heap property.
  @   axiom is_heap_def{L}:
  @     \forall int (*heap)[2], int size;
  @       is_heap(heap, size) <==>
  @         (size == 0 || size == 1 ||
  @          (\forall integer i; 0 <= i < size / 2 ==>
  @             (is_heap(heap, 2 * i + 1) &&
  @              (2 * i + 2 >= size || is_heap(heap, 2 * i + 2)))));
  @
  @   // A max-heap is a heap where parent is greater than or equal to children.
  @   axiom is_max_heap_def{L}:
  @     \forall int (*heap)[2], int size;
  @       is_max_heap(heap, size) <==>
  @         (is_heap(heap, size) &&
  @          (\forall integer i; 0 <= i < size / 2 ==>
  @             (heap[i][0] >= heap[2 * i + 1][0] &&
  @              (2 * i + 2 >= size || heap[i][0] >= heap[2 * i + 2][0]))));
  @
  @   // A min-heap is a heap where parent is less than or equal to children.
  @   axiom is_min_heap_def{L}:
  @     \forall int (*heap)[2], int size;
  @       is_min_heap(heap, size) <==>
  @         (is_heap(heap, size) &&
  @          (\forall integer i; 0 <= i < size / 2 ==>
  @             (heap[i][0] <= heap[2 * i + 1][0] &&
  @              (2 * i + 2 >= size || heap[i][0] <= heap[2 * i + 2][0]))));
  @
  @   // Helper axiom: values in a min-heap are >= root
  @   axiom min_heap_root_min{L}:
  @     \forall int (*heap)[2], int size;
  @       is_min_heap(heap, size) && size > 0 ==>
  @         \forall integer i; 0 <= i < size ==> heap[0][0] <= heap[i][0];
  @
  @   // Helper axiom: values in a max-heap are <= root
  @   axiom max_heap_root_max{L}:
  @     \forall int (*heap)[2], int size;
  @       is_max_heap(heap, size) && size > 0 ==>
  @         \forall integer i; 0 <= i < size ==> heap[0][0] >= heap[i][0];
  @ }
  @*/

/*@
  @ requires \valid(heap);
  @ requires \valid_range(heap, 0, size - 1);
  @ requires 0 <= idx < size;
  @ requires 0 <= size <= max_size;
  @ requires is_min_heap(heap, size); // Pre-condition for min_heapify_up
  @
  @ assigns heap[0..size-1];
  @
  @ ensures is_min_heap(heap, size);
  @ ensures \forall integer k; 0 <= k < size ==>
  @   \at(heap[k][0], Pre) == (if k == idx_orig then \at(heap[parent_idx_orig][0], Pre) else (if k == parent_idx_orig then \at(heap[idx_orig][0], Pre) else \at(heap[k][0], Pre)));
  @ ensures \forall integer k; 0 <= k < size ==>
  @   \at(heap[k][1], Pre) == (if k == idx_orig then \at(heap[parent_idx_orig][1], Pre) else (if k == parent_idx_orig then \at(heap[idx_orig][1], Pre) else \at(heap[k][1], Pre)));
  @
  @ behavior not_root:
  @   assumes idx > 0;
  @   assigns heap[0..size-1];
  @   ensures \at(heap[idx][0], Post) == \at(heap[idx][0], Pre) || \at(heap[idx][0], Post) == \at(heap[parent_idx_orig][0], Pre);
  @   ensures \at(heap[idx][1], Post) == \at(heap[idx][1], Pre) || \at(heap[idx][1], Post) == \at(heap[parent_idx_orig][1], Pre);
  @   ensures \at(heap[parent_idx_orig][0], Post) == \at(heap[idx][0], Pre) || \at(heap[parent_idx_orig][0], Post) == \at(heap[parent_idx_orig][0], Pre);
  @   ensures \at(heap[parent_idx_orig][1], Post) == \at(heap[idx][1], Pre) || \at(heap[parent_idx_orig][1], Post) == \at(heap[parent_idx_orig][1], Pre);
  @
  @ behavior is_root:
  @   assumes idx == 0;
  @   assigns \nothing;
  @   ensures \forall integer k; 0 <= k < size ==> heap[k][0] == \at(heap[k][0], Pre);
  @   ensures \forall integer k; 0 <= k < size ==> heap[k][1] == \at(heap[k][1], Pre);
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
static void min_heapify_up(int (*heap)[2], int size, int max_size, int idx) {
    /*@ ghost int idx_orig = idx; */
    /*@ ghost int parent_idx_orig = (idx - 1) / 2; */
    /*@
      @ loop invariant 0 <= idx < size;
      @ loop invariant parent_idx == (idx - 1) / 2;
      @ loop invariant is_min_heap(heap, size);
      @ loop invariant \forall integer k; 0 <= k < size && k != idx && k != parent_idx ==> heap[k][0] == \at(heap[k][0], Pre);
      @ loop invariant \forall integer k; 0 <= k < size && k != idx && k != parent_idx ==> heap[k][1] == \at(heap[k][1], Pre);
      @ loop assigns idx, heap[0..size-1];
      @ loop variant idx;
    */
    while (idx > 0) {
        int parent_idx = (idx - 1) / 2;
        if (heap[idx][0] < heap[parent_idx][0]) {
            int temp_freq = heap[idx][0];
            int temp_val = heap[idx][1];
            heap[idx][0] = heap[parent_idx][0];
            heap[idx][1] = heap[parent_idx][1];
            heap[parent_idx][0] = temp_freq;
            heap[parent_idx][1] = temp_val;
            idx = parent_idx;
        } else {
            break;
        }
    }
}

/*@
  @ requires \valid(heap);
  @ requires \valid_range(heap, 0, size - 1);
  @ requires 0 <= idx < size;
  @ requires 0 <= size <= max_size;
  @ requires is_min_heap(heap, size); // Pre-condition for min_heapify_down
  @
  @ assigns heap[0..size-1];
  @
  @ ensures is_min_heap(heap, size);
  @ ensures \forall integer k; 0 <= k < size ==>
  @   \at(heap[k][0], Post) == \at(heap[k][0], Pre) || // Either unchanged or moved
  @   (\exists integer j; 0 <= j < size && \at(heap[k][0], Post) == \at(heap[j][0], Pre));
  @ ensures \forall integer k; 0 <= k < size ==>
  @   \at(heap[k][1], Post) == \at(heap[k][1], Pre) ||
  @   (\exists integer j; 0 <= j < size && \at(heap[k][1], Post) == \at(heap[j][1], Pre));
  @*/
static void min_heapify_down(int (*heap)[2], int size, int max_size, int idx) {
    /*@
      @ loop invariant 0 <= idx < size;
      @ loop invariant left_child_idx == 2 * idx + 1;
      @ loop invariant right_child_idx == 2 * idx + 2;
      @ loop invariant is_min_heap(heap, size);
      @ loop assigns idx, heap[0..size-1];
      @ loop variant size - idx;
    */
    while (2 * idx + 1 < size) {
        int left_child_idx = 2 * idx + 1;
        int right_child_idx = 2 * idx + 2;
        int smallest_idx = idx;

        if (left_child_idx < size && heap[left_child_idx][0] < heap[smallest_idx][0]) {
            smallest_idx = left_child_idx;
        }
        if (right_child_idx < size && heap[right_child_idx][0] < heap[smallest_idx][0]) {
            smallest_idx = right_child_idx;
        }

        if (smallest_idx != idx) {
            int temp_freq = heap[idx][0];
            int temp_val = heap[idx][1];
            heap[idx][0] = heap[smallest_idx][0];
            heap[idx][1] = heap[smallest_idx][1];
            heap[smallest_idx][0] = temp_freq;
            heap[smallest_idx][1] = temp_val;
            idx = smallest_idx;
        } else {
            break;
        }
    }
}

/*@
  @ requires \valid(heap);
  @ requires \valid_range(heap, 0, size - 1);
  @ requires 0 <= size < max_size;
  @ requires max_size > 0;
  @ requires is_min_heap(heap, size);
  @
  @ assigns heap[0..size];
  @
  @ ensures is_min_heap(heap, size + 1);
  @ ensures \exists integer k; 0 <= k <= size && heap[k][0] == freq && heap[k][1] == val;
  @ ensures \forall integer k; 0 <= k < size ==> (\exists integer j; 0 <= j < size+1 && heap[j][0] == \at(heap[k][0], Pre) && heap[j][1] == \at(heap[k][1], Pre));
  @*/
static void min_heap_insert(int (*heap)[2], int* size, int max_size, int freq, int val) {
    heap[*size][0] = freq;
    heap[*size][1] = val;
    min_heapify_up(heap, *size + 1, max_size, *size);
    (*size)++;
}

/*@
  @ requires \valid(heap);
  @ requires \valid_range(heap, 0, size - 1);
  @ requires size > 0;
  @ requires is_min_heap(heap, size);
  @
  @ assigns heap[0..size-1];
  @
  @ ensures is_min_heap(heap, size - 1);
  @ ensures \result == \at(heap[0][1], Pre);
  @ ensures \forall integer k; 0 <= k < size-1 ==> (\exists integer j; 1 <= j < size && heap[k][0] == \at(heap[j][0], Pre) && heap[k][1] == \at(heap[j][1], Pre)) || (\exists integer j; 1 <= j < size && heap[k][0] == \at(heap[0][0], Pre) && heap[k][1] == \at(heap[0][1], Pre));
  @*/
static int min_heap_extract_min(int (*heap)[2], int* size, int max_size) {
    int min_val = heap[0][1];
    heap[0][0] = heap[*size - 1][0];
    heap[0][1] = heap[*size - 1][1];
    (*size)--;
    min_heapify_down(heap, *size, max_size, 0);
    return min_val;
}

/*@
  @ requires \valid(total_arr);
  @ requires total_size >= 0;
  @ requires \valid(result);
  @ requires k >= 0;
  @ requires \valid_range(result, 0, k - 1);
  @
  @ // Sum of all occurrences for each unique value does not exceed total_size.
  @ // This prevents potential overflow issues if frequencies are very large.
  @ // (Although frequencies can't exceed total_size anyway).
  @ requires total_size < 46340 * 46340; // Max size for sum of frequencies to avoid overflow during comparison
  @
  @ assigns result[0..k-1], total_arr[0..total_size-1];
  @
  @ behavior k_zero:
  @   assumes k == 0;
  @   assigns \nothing;
  @   ensures \forall integer i; 0 <= i < total_size ==> total_arr[i] == \at(total_arr[i], Pre);
  @   ensures \forall integer i; 0 <= i < k ==> result[i] == \at(result[i], Pre); // No change to result if k=0
  @
  @ behavior normal:
  @   assumes k > 0;
  @   assigns result[0..k-1], total_arr[0..total_size-1];
  @   ensures \forall integer i; 0 <= i < k ==> \exists integer val; count_occurrence(val, total_arr, total_size) > 0 && \result[i] == val;
  @   ensures \forall integer i; 0 <= i < k ==>
  @     (\forall integer j; 0 <= j < k && j != i ==>
  @       (count_occurrence(\result[i], total_arr, total_size) >= count_occurrence(\result[j], total_arr, total_size)));
  @   ensures \forall integer val_not_in_result;
  @     (\forall integer i; 0 <= i < k ==> val_not_in_result != \result[i]) ==>
  @       (count_occurrence(val_not_in_result, total_arr, total_size) <= count_occurrence(\result[k-1], total_arr, total_size));
  @
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
void find_top_k_frequent(int* total_arr, int total_size, int k, int* result) {
    if (k == 0) {
        return;
    }

    // Using a 2D array for the min-heap: [frequency, value]
    // Max k is 1000, so heap_storage[1000][2] is safe.
    // Rule II.5: ensure k is not too large for stack allocation
    /*@ requires k <= 1000; */
    int heap_storage[1000][2];
    int heap_size = 0;

    int current_val = 0;
    int current_count = 0;

    /*@
      @ loop invariant 0 <= i <= total_size;
      @ loop invariant i == 0 ==> current_count == 0 && current_val == 0;
      @ loop invariant i > 0 ==> \forall integer j; 0 <= j < i-1 ==> total_arr[j] <= total_arr[j+1]; // input is sorted
      @ loop invariant i > 0 ==> current_val == total_arr[i-1];
      @ loop invariant i > 0 ==> current_count == count_occurrence(current_val, total_arr, i) - count_occurrence(current_val, total_arr, i-current_count);
      @ // Min-heap property for heap_storage
      @ loop invariant is_min_heap(heap_storage, heap_size);
      @ // All elements in the heap are distinct
      @ loop invariant \forall integer m, n; 0 <= m < heap_size && 0 <= n < heap_size && m != n ==> heap_storage[m][1] != heap_storage[n][1];
      @ // All elements in the heap have a count > 0
      @ loop invariant \forall integer m; 0 <= m < heap_size ==> heap_storage[m][0] > 0;
      @ // If heap is full, its min element has frequency less than or equal to current_count
      @ loop invariant heap_size == k ==> heap_storage[0][0] <= current_count;
      @ // All processed unique elements are either in the heap or were removed because their frequency was too low
      @ loop invariant \forall integer val;
      @   (\exists integer j; 0 <= j < i && total_arr[j] == val) && count_occurrence(val, total_arr, i) > 0 ==>
      @     (\exists integer m; 0 <= m < heap_size && heap_storage[m][1] == val) ||
      @     (heap_size == k && count_occurrence(val, total_arr, i) <= heap_storage[0][0]);
      @
      @ loop assigns i, current_val, current_count, heap_storage[0..k-1], heap_size;
      @ loop variant total_size - i;
    */
    for (int i = 0; i < total_size; i++) {
        if (i == 0 || total_arr[i] != current_val) {
            // New distinct element encountered
            if (current_count > 0) { // Process the previous distinct element
                if (heap_size < k) {
                    min_heap_insert(heap_storage, &heap_size, k, current_count, current_val);
                } else if (current_count > heap_storage[0][0]) {
                    (void)min_heap_extract_min(heap_storage, &heap_size, k); // Discard return value
                    min_heap_insert(heap_storage, &heap_size, k, current_count, current_val);
                }
            }
            current_val = total_arr[i];
            current_count = 1;
        } else {
            // Same element, increment count
            current_count++;
        }
    }

    // Process the last distinct element
    /*@
      @ requires total_size == 0 || (current_count > 0 && current_val == total_arr[total_size-1]);
      @ requires is_min_heap(heap_storage, heap_size);
      @ requires heap_size <= k;
      @ assigns heap_storage[0..k-1], heap_size;
      @ ensures is_min_heap(heap_storage, heap_size);
    */
    if (current_count > 0) {
        if (heap_size < k) {
            min_heap_insert(heap_storage, &heap_size, k, current_count, current_val);
        } else if (current_count > heap_storage[0][0]) {
            (void)min_heap_extract_min(heap_storage, &heap_size, k);
            min_heap_insert(heap_storage, &heap_size, k, current_count, current_val);
        }
    }

    // Extract elements from the min-heap to fill the result array in reverse order
    /*@
      @ loop invariant 0 <= j <= heap_size_orig;
      @ loop invariant heap_size == heap_size_orig - j;
      @ loop invariant is_min_heap(heap_storage, heap_size);
      @ loop invariant \forall integer m; 0 <= m < heap_size_orig - j ==> (\exists integer idx; 0 <= idx < heap_size_orig && heap_storage[m][1] == \at(heap_storage[idx][1], Pre));
      @ loop invariant \forall integer m; heap_size_orig - j <= m < heap_size_orig ==> (\exists integer idx; 0 <= idx < heap_size_orig && result[m] == \at(heap_storage[idx][1], Pre));
      @ loop assigns j, heap_storage[0..k-1], heap_size, result[0..k-1];
      @ loop variant j;
    */
    /*@ ghost int heap_size_orig = heap_size; */
    for (int j = 0; j < heap_size_orig; j++) {
        result[heap_size_orig - 1 - j] = min_heap_extract_min(heap_storage, &heap_size, k);
    }
}
