// Task ID: 31
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in ACSL logic.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@ axiomatic IntegerList {
  logic integer list_length{L}(int* list, integer start_idx, integer end_idx);

  axiom list_length_empty{L}:
    \forall int* list, integer start_idx, end_idx;
      start_idx >= end_idx ==> list_length(list, start_idx, end_idx) == 0;

  axiom list_length_recursive{L}:
    \forall int* list, integer start_idx, end_idx;
      start_idx < end_idx ==> list_length(list, start_idx, end_idx) == 1 + list_length(list, start_idx + 1, end_idx);

  // Helper axiom for list_length
  axiom list_length_positive{L}:
    \forall int* list, integer start_idx, end_idx;
      start_idx < end_idx ==> list_length(list, start_idx, end_idx) > 0;

  logic int is_sorted{L}(int* list, integer start_idx, integer end_idx);

  axiom is_sorted_empty{L}:
    \forall int* list, integer start_idx, end_idx;
      start_idx >= end_idx ==> is_sorted(list, start_idx, end_idx) == 1;

  axiom is_sorted_one_element{L}:
    \forall int* list, integer start_idx;
      is_sorted(list, start_idx, start_idx + 1) == 1;

  axiom is_sorted_recursive{L}:
    \forall int* list, integer start_idx, end_idx;
      start_idx + 1 < end_idx ==> (is_sorted(list, start_idx, end_idx) == (if list[start_idx] <= list[start_idx+1] && is_sorted(list, start_idx+1, end_idx) == 1 then 1 else 0));

  logic int has_distinct_elements{L}(int* list, integer start_idx, integer end_idx);

  axiom has_distinct_elements_empty{L}:
    \forall int* list, integer start_idx, end_idx;
      start_idx >= end_idx ==> has_distinct_elements(list, start_idx, end_idx) == 1;

  axiom has_distinct_elements_one_element{L}:
    \forall int* list, integer start_idx;
      has_distinct_elements(list, start_idx, start_idx + 1) == 1;

  axiom has_distinct_elements_recursive{L}:
    \forall int* list, integer start_idx, end_idx;
      start_idx + 1 < end_idx ==> (has_distinct_elements(list, start_idx, end_idx) == (if list[start_idx] != list[start_idx+1] && has_distinct_elements(list, start_idx+1, end_idx) == 1 then 1 else 0));
} */

/*@ axiomatic Heap {
  // A pair of (value, count)
  struct Pair {
    int value;
    int count;
  };

  // Represents a min-heap where elements are Pair structs, ordered by count (min-heap).
  // If counts are equal, order by value (min-heap).
  // The heap is stored in an array `heap` of size `capacity`.
  // `size` is the current number of elements in the heap.

  // Helper function to check if an index is valid within the heap's current size.
  logic int is_valid_index(integer idx, integer size) = idx >= 0 && idx < size;

  // Helper function to get the left child index.
  logic integer left_child(integer idx) = 2 * idx + 1;

  // Helper function to get the right child index.
  logic integer right_child(integer idx) = 2 * idx + 2;

  // Helper function to get the parent index.
  logic integer parent(integer idx) = (idx - 1) / 2;

  // Checks if the given index `idx` has a left child within the heap's current size.
  logic int has_left_child(integer idx, integer size) = is_valid_index(left_child(idx), size);

  // Checks if the given index `idx` has a right child within the heap's current size.
  logic int has_right_child(integer idx, integer size) = is_valid_index(right_child(idx), size);

  // Checks if the given index `idx` has a parent within the heap's current size.
  logic int has_parent(integer idx) = idx > 0;

  // Compares two pairs for min-heap property: first by count (ascending), then by value (ascending).
  // Returns 1 if p1 should come before p2 (p1 < p2), 0 otherwise.
  logic int pair_less(struct Pair p1, struct Pair p2) =
    (if p1.count < p2.count then 1
     else if p1.count == p2.count then (if p1.value < p2.value then 1 else 0)
     else 0);

  // Checks if the heap property holds for a subtree rooted at `idx`.
  // This is a recursive definition.
  logic int is_min_heap_property_at{L}(struct Pair* heap, integer size, integer idx) =
    (if !is_valid_index(idx, size) then 1 // Base case: invalid index (e.g., beyond size) is vacuously true.
     else if !has_left_child(idx, size) then 1 // Base case: no children, property holds.
     else if has_right_child(idx, size) then // Has both children
       pair_less(heap[idx], heap[left_child(idx)]) == 1 &&
       pair_less(heap[idx], heap[right_child(idx)]) == 1 &&
       is_min_heap_property_at(heap, size, left_child(idx)) == 1 &&
       is_min_heap_property_at(heap, size, right_child(idx)) == 1
     else // Has only left child
       pair_less(heap[idx], heap[left_child(idx)]) == 1 &&
       is_min_heap_property_at(heap, size, left_child(idx)) == 1);

  // Checks if the entire array `heap` up to `size` forms a min-heap.
  logic int is_min_heap{L}(struct Pair* heap, integer size) =
    (if size <= 1 then 1 // Empty or single-element heap is always a min-heap.
     else is_min_heap_property_at(heap, size, 0) == 1);

  // Helper axiom for is_min_heap_property_at: if parent holds, children hold.
  axiom is_min_heap_property_at_parent_implies_children{L}:
    \forall struct Pair* heap, integer size, integer idx;
      is_valid_index(idx, size) && has_left_child(idx, size) && is_min_heap_property_at(heap, size, idx) == 1 ==>
        is_min_heap_property_at(heap, size, left_child(idx)) == 1;

  axiom is_min_heap_property_at_parent_implies_right_child{L}:
    \forall struct Pair* heap, integer size, integer idx;
      is_valid_index(idx, size) && has_right_child(idx, size) && is_min_heap_property_at(heap, size, idx) == 1 ==>
        is_min_heap_property_at(heap, size, right_child(idx)) == 1;
} */

/*@
  requires \valid_read(arr_sizes);
  requires \valid_read(arr_lists + (0..num_lists-1));
  requires \forall integer i; 0 <= i < num_lists ==> \valid_read(arr_lists[i] + (0..arr_sizes[i]-1));
  requires \forall integer i; 0 <= i < num_lists ==> arr_sizes[i] >= 0;
  requires num_lists >= 0;
  requires k >= 0;

  // Constraint to prevent overflow in counts or values, assuming int.
  requires \forall integer i, j; 0 <= i < num_lists && 0 <= j < arr_sizes[i] ==> arr_lists[i][j] >= -1000000 && arr_lists[i][j] <= 1000000;
  requires \forall integer i, j; 0 <= i < num_lists ==> is_sorted(arr_lists[i], 0, arr_sizes[i]) == 1;
  requires \forall integer i, j; 0 <= i < num_lists ==> has_distinct_elements(arr_lists[i], 0, arr_sizes[i]) == 1;

  // Output buffer for results
  requires \valid(result + (0..k-1));
  requires \separated(arr_lists[0..num_lists-1], result+(0..k-1));

  // Temporary heap buffer
  requires \valid(heap_storage + (0..k-1));
  requires \separated(heap_storage+(0..k-1), result+(0..k-1));
  requires \separated(heap_storage+(0..k-1), arr_lists[0..num_lists-1]);

  assigns result[0..k-1], heap_storage[0..k-1];
*/
void find_top_k_frequent(int* const arr_lists[], const int arr_sizes[], int num_lists, int k, int result[], struct Pair heap_storage[]) {

    // Initialize the heap size
    int heap_size = 0;

    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant \forall integer m; 0 <= m < i ==>
        \forall integer n; 0 <= n < arr_sizes[m] ==>
          (is_min_heap(heap_storage, heap_size) == 1); // Heap property is always maintained
      loop invariant 0 <= heap_size <= k;
      loop assigns i, heap_size, heap_storage[0..k-1];
      loop variant num_lists - i;
    */
    for (int i = 0; i < num_lists; ++i) {
        /*@
          loop invariant 0 <= j <= arr_sizes[i];
          loop invariant \forall integer m; 0 <= m < i ==>
            \forall integer n; 0 <= n < arr_sizes[m] ==>
              (is_min_heap(heap_storage, heap_size) == 1);
          loop invariant 0 <= heap_size <= k;
          loop invariant is_min_heap(heap_storage, heap_size) == 1;
          loop assigns j, heap_size, heap_storage[0..k-1];
          loop variant arr_sizes[i] - j;
        */
        for (int j = 0; j < arr_sizes[i]; ++j) {
            int current_val = arr_lists[i][j];
            int current_count = 1; // Since elements are distinct in each list

            // Find the frequency of current_val across all remaining lists
            /*@
              loop invariant j < l_idx <= arr_sizes[i];
              loop invariant current_count == (\num_of(integer x; j <= x < l_idx && arr_lists[i][x] == arr_lists[i][j]));
              loop assigns l_idx, current_count;
              loop variant arr_sizes[i] - l_idx;
            */
            for (int l_idx = j + 1; l_idx < arr_sizes[i]; ++l_idx) {
                if (arr_lists[i][l_idx] == current_val) {
                    current_count++;
                } else {
                    break; // Lists are sorted and distinct, so we can break
                }
            }
            j += current_count - 1; // Advance j to skip already counted elements

            struct Pair new_pair = { .value = current_val, .count = current_count };

            if (heap_size < k) {
                // Add to heap
                heap_storage[heap_size] = new_pair;
                heap_size++;

                // Heapify up
                /*@
                  loop invariant 0 <= current <= heap_size;
                  loop invariant is_min_heap_property_at(heap_storage, heap_size, current) == 1; // Current subtree holds property
                  loop invariant \forall integer m; current < m < heap_size ==> is_min_heap_property_at(heap_storage, heap_size, m) == 1; // Siblings and children also hold property
                  loop invariant \forall integer m; 0 <= m < heap_size && m != current && m != parent(current) ==> \at(heap_storage[m], Pre) == heap_storage[m]; // Other elements unchanged
                  loop assigns heap_storage[0..heap_size-1], current;
                  loop variant current;
                */
                int current = heap_size - 1;
                while (current > 0 && pair_less(heap_storage[current], heap_storage[parent(current)]) == 1) {
                    // Swap
                    struct Pair temp = heap_storage[parent(current)];
                    heap_storage[parent(current)] = heap_storage[current];
                    heap_storage[current] = temp;
                    current = parent(current);
                }
            } else if (k > 0 && (pair_less(heap_storage[0], new_pair) == 0)) { // Only replace if new_pair is "larger" than root
                // Replace root and heapify down
                heap_storage[0] = new_pair;

                /*@
                  loop invariant 0 <= current < heap_size;
                  loop invariant is_min_heap_property_at(heap_storage, heap_size, current) == 1; // Current subtree holds property
                  loop invariant \forall integer m; 0 <= m < heap_size && m != current && m != left_child(current) && m != right_child(current) ==> \at(heap_storage[m], Pre) == heap_storage[m]; // Other elements unchanged
                  loop assigns heap_storage[0..heap_size-1], current;
                  loop variant (heap_size - current) * 2; // Rough estimate of depth
                */
                int current = 0;
                while (has_left_child(current, heap_size) == 1) {
                    int smallest_child_idx = left_child(current);
                    if (has_right_child(current, heap_size) == 1 && pair_less(heap_storage[right_child(current)], heap_storage[smallest_child_idx]) == 1) {
                        smallest_child_idx = right_child(current);
                    }

                    if (pair_less(heap_storage[smallest_child_idx], heap_storage[current]) == 1) {
                        // Swap
                        struct Pair temp = heap_storage[current];
                        heap_storage[current] = heap_storage[smallest_child_idx];
                        heap_storage[smallest_child_idx] = temp;
                        current = smallest_child_idx;
                    } else {
                        break;
                    }
                }
            }
        }
    }

    // Extract top k elements from the heap (they are already in the heap_storage array)
    // The problem asks for the top k, not necessarily sorted by frequency.
    // So, we just copy them as they are in the min-heap.
    /*@
      loop invariant 0 <= i <= heap_size;
      loop invariant \forall integer m; 0 <= m < i ==> result[m] == heap_storage[m].value;
      loop assigns result[0..heap_size-1], i;
      loop variant heap_size - i;
    */
    for (int i = 0; i < heap_size; ++i) {
        result[i] = heap_storage[i].value;
    }

    // Fill remaining result slots with 0 if k > heap_size
    /*@
      loop invariant heap_size <= i <= k;
      loop invariant \forall integer m; heap_size <= m < i ==> result[m] == 0;
      loop assigns result[heap_size..k-1], i;
      loop variant k - i;
    */
    for (int i = heap_size; i < k; ++i) {
        result[i] = 0;
    }
}
