// Task ID: 23
// Generation: 6

/*@
  // Rule II.1: Define recursive logic for sum of elements in an array.
  axiomatic SumArray {
    logic integer sum_array_elements{L}(int* arr, int size);

    // Base case: sum of an empty array is 0.
    axiom sum_array_empty{L}:
      \forall int* arr, int size;
        size <= 0 ==> sum_array_elements(arr, size) == 0;

    // Recursive case: sum is current element + sum of rest.
    axiom sum_array_recursive{L}:
      \forall int* arr, int size;
        size > 0 ==> sum_array_elements(arr, size) == arr[size - 1] + sum_array_elements(arr, size - 1);

    // Rule II.2: Helper axiom for sum bounds.
    // If all elements are non-negative, their sum is non-negative.
    axiom sum_array_non_negative{L}:
      \forall int* arr, int size;
        (\forall integer k; 0 <= k < size ==> arr[k] >= 0) ==> sum_array_elements(arr, size) >= 0;

    // If all elements are within a range [min_val, max_val], then sum is within [size*min_val, size*max_val].
    axiom sum_array_bounds{L}:
      \forall int* arr, int size, int min_val, int max_val;
        (\forall integer k; 0 <= k < size ==> min_val <= arr[k] <= max_val) ==>
        (integer)size * min_val <= sum_array_elements(arr, size) <= (integer)size * max_val;
  }
*/

/*@
  requires num_lists >= 0;
  requires num_cols >= 0;

  // Rule II.5: Prevent potential overflow if sums are very large.
  // Assuming int is 32-bit, max sum is around 2*10^9.
  // If each element is INT_MAX (approx 2*10^9), and num_cols is 1, then sum could be INT_MAX.
  // If num_cols is larger, we need to constrain element values.
  // A conservative bound: if max_val for elements is 1000, and num_cols is 1000, sum is 10^6.
  // If num_lists * num_cols is very large, the sum could exceed INT_MAX.
  // For simplicity, let's assume individual sums will not overflow int, and the max of these sums also won't.
  // This requires user to ensure element values and sizes are reasonable.
  // More precise: ensure that max possible sum_array_elements(lists[i], num_cols) fits in int.
  // For example, if elements are positive, ensure sum_array_elements(lists[i], num_cols) <= INT_MAX.
  // If elements can be negative, the range is wider.
  // For this problem, we will assume that the sum of elements in any sublist fits within an `int`.
  // And also that the maximum of these sums fits within an `int`.
  // No explicit `requires` for sum overflow here, as it depends on actual element values,
  // which are not directly constrained by `num_cols`.

  // Rule I.3: Array parameter `lists` decays to a pointer to an array of size `num_cols`.
  // The `assigns` clause for `max_sum_of_lists` indicates it does not modify any global state.
  assigns \nothing;

  // Rule II.3: The ensures clause uses logical equivalence for the return value.
  ensures \result == (\max integer k; 0 <= k < num_lists; sum_array_elements(lists[k], num_cols));
*/
int max_sum_of_lists(int lists[][num_cols], int num_lists, int num_cols) {
    if (num_lists <= 0) {
        return 0; // Or some other appropriate default/error value if no lists.
    }

    // Initialize max_so_far with the sum of the first list.
    // Assuming num_lists > 0 when this line is reached.
    int max_so_far = sum_array_elements(lists[0], num_cols);

    /*@
      loop invariant 0 <= i <= num_lists;
      // The `max_so_far` variable correctly holds the maximum sum found among the lists processed so far.
      loop invariant max_so_far == (\max integer k; 0 <= k < i; sum_array_elements(lists[k], num_cols));
      loop assigns i, max_so_far;
      loop variant num_lists - i;
    */
    for (int i = 1; i < num_lists; i++) {
        int current_sum = sum_array_elements(lists[i], num_cols);
        if (current_sum > max_so_far) {
            max_so_far = current_sum;
        }
    }

    return max_so_far;
}
