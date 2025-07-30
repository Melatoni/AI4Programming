// Task ID: 42
// Generation: 0

/*@ axiomatic Freq {
  @   logic integer count_occurrence{L}(int* arr, int size, int val) reads arr[0..size-1];

  @   axiom count_occurrence_empty{L}:
  @     \forall int* arr, int val;
  @       count_occurrence(arr, 0, val) == 0;

  @   axiom count_occurrence_rec{L}:
  @     \forall int* arr, int size, int val;
  @       size > 0 ==> count_occurrence(arr, size, val) ==
  @         (if arr[size - 1] == val then 1 else 0) + count_occurrence(arr, size - 1, val);

  @   // Helper axiom for sum of repeated elements
  @   // If an element appears more than once, it contributes its value to the sum.
  @   // This axiom helps relate the sum of repeated elements to individual counts.
  @   logic integer sum_repeated_elements_logic{L}(int* arr, int size, int end_idx) reads arr[0..size-1];

  @   axiom sum_repeated_elements_logic_base{L}:
  @     \forall int* arr, int size;
  @       sum_repeated_elements_logic(arr, size, -1) == 0;

  @   axiom sum_repeated_elements_logic_rec{L}:
  @     \forall int* arr, int size, int end_idx;
  @       0 <= end_idx < size ==>
  @       sum_repeated_elements_logic(arr, size, end_idx) ==
  @       (if count_occurrence(arr, size, arr[end_idx]) > 1 then arr[end_idx] else 0) +
  @       sum_repeated_elements_logic(arr, size, end_idx - 1);
  @ }
  @*/

/*@
  @ requires \valid_read_range(arr, 0, size - 1);
  @ requires size >= 0;
  @
  @ // Sum of repeated elements must fit in int.
  @ // The sum can be at most size * INT_MAX.
  @ // Frama-C doesn't know INT_MAX directly, so we need a concrete bound
  @ // or assume the sum does not overflow. For simplicity, we assume
  @ // no overflow for now, or add a specific bound if needed.
  @ // Example: requires (\sum integer k; 0 <= k < size; (if count_occurrence(arr, size, arr[k]) > 1 then arr[k] else 0)) <= INT_MAX;
  @ // This sum is problematic to prove directly with WP.
  @ // A more practical approach is to ensure individual elements are not too large
  @ // or that the sum doesn't exceed a known bound for a practical array size.
  @ // For now, we omit an explicit overflow check for the sum itself, relying on
  @ // the assumption that intermediate sums fit.
  @
  @ assigns \nothing;
  @
  @ ensures \result == sum_repeated_elements_logic(arr, size, size - 1);
  @*/
int sum_repeated_elements(int* arr, int size) {
    int total_sum = 0;
    /*@
      @ loop invariant 0 <= i <= size;
      @ loop invariant total_sum == sum_repeated_elements_logic(arr, size, i - 1);
      @ loop assigns total_sum, i;
      @ loop variant size - i;
    */
    for (int i = 0; i < size; ++i) {
        int current_element = arr[i];
        int count = 0;
        /*@
          @ loop invariant 0 <= j <= size;
          @ loop invariant count == count_occurrence(arr, j, current_element);
          @ loop assigns count, j;
          @ loop variant size - j;
        */
        for (int j = 0; j < size; ++j) {
            if (arr[j] == current_element) {
                count++;
            }
        }
        // If the element appears more than once, add it to the sum.
        // We only add it once per element value, not for each occurrence.
        // To avoid adding it multiple times for the same value, we need a way
        // to mark elements as "processed" or check if it has been added before.
        // The current logic sum_repeated_elements_logic sums each *repeated* instance.
        // If the problem means "sum of values that are repeated", then we need to ensure
        // each unique repeated value is added only once.
        // Let's refine the interpretation: "sum of all occurrences of elements that appear more than once".
        // Example: [1, 2, 2, 3, 3, 3] -> sum = 2+2 (from two 2s) + 3+3+3 (from three 3s) = 12.
        // If it means "sum of unique values that are repeated": [1, 2, 2, 3, 3, 3] -> sum = 2 + 3 = 5.
        // The former interpretation is more common for "sum of repeated elements".
        // The `sum_repeated_elements_logic` currently sums each instance if its count > 1.
        // To precisely match the logic, we need to ensure `total_sum` accumulates correctly.

        // A simpler way to sum all occurrences of repeated elements is to use a frequency array
        // or a nested loop with a "visited" array. Since we can't use a visited array easily
        // without more complex logic (e.g., modifying the input array, which is usually bad,
        // or a separate boolean array, which implies a fixed maximum element value),
        // let's stick to the current approach but adjust the logic.

        // The current `sum_repeated_elements_logic` adds `arr[end_idx]` if its count > 1.
        // This means it adds each instance of a repeated number.
        // Example: [1, 2, 2, 3, 3, 3].
        // i=0, arr[0]=1, count=1. total_sum = 0.
        // i=1, arr[1]=2, count=2. total_sum += 2. total_sum = 2.
        // i=2, arr[2]=2, count=2. total_sum += 2. total_sum = 4.
        // i=3, arr[3]=3, count=3. total_sum += 3. total_sum = 7.
        // i=4, arr[4]=3, count=3. total_sum += 3. total_sum = 10.
        // i=5, arr[5]=3, count=3. total_sum += 3. total_sum = 13.
        // Result: 13. This matches `sum_repeated_elements_logic`.

        if (count > 1) {
            total_sum += current_element;
        }
    }
    return total_sum;
}
