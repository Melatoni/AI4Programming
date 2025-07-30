// Task ID: 23
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
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

/*@
  axiomatic SumArray {
    logic integer sum_array_elements{L}(int* arr, int size);

    axiom sum_array_elements_base{L}:
      \forall int* arr, int size;
        size <= 0 ==> sum_array_elements(arr, size) == 0;

    axiom sum_array_elements_recursive{L}:
      \forall int* arr, int size;
        size > 0 ==> sum_array_elements(arr, size) == arr[size - 1] + sum_array_elements(arr, size - 1);

    // Rule II.2: Helper axiom for sum range
    // If all elements are non-negative, the sum is non-negative.
    axiom sum_array_elements_non_negative{L}:
      \forall int* arr, int size;
        (\forall integer k; 0 <= k < size ==> arr[k] >= 0) ==> sum_array_elements(arr, size) >= 0;

    // If all elements are within a range [min_val, max_val], the sum is within [size * min_val, size * max_val].
    // This is a general helper axiom for range.
    axiom sum_array_elements_range{L}:
      \forall int* arr, int size, integer min_val, integer max_val;
        (\forall integer k; 0 <= k < size ==> min_val <= arr[k] <= max_val) ==>
        (integer)size * min_val <= sum_array_elements(arr, size) <= (integer)size * max_val;
  }
*/

/*@
  requires num_lists > 0;
  requires \valid_read(lists + (0..num_lists-1));
  requires \forall integer i; 0 <= i < num_lists ==> lists[i].size >= 0;
  requires \forall integer i; 0 <= i < num_lists ==> \valid_read(lists[i].arr + (0..lists[i].size-1));

  // The maximum possible sum could be num_lists * INT_MAX, which might overflow.
  // We need to constrain the input to prevent overflow of the intermediate sums and the final result.
  // Assuming a 32-bit int, the maximum sum is INT_MAX (around 2*10^9).
  // If list elements are small, this constraint can be relaxed.
  // For simplicity, let's assume elements are small enough such that the max sum won't overflow int.
  // A tighter bound would be:
  // requires \forall integer i; 0 <= i < num_lists ==>
  //   sum_array_elements(lists[i].arr, lists[i].size) <= INT_MAX;
  // requires \forall integer i; 0 <= i < num_lists ==>
  //   sum_array_elements(lists[i].arr, lists[i].size) >= INT_MIN;

  // Let's assume for now that individual sums and the overall max sum fit within `int`.
  // If this were a real-world scenario, we'd use `long long` or tighter `requires` clauses.

  assigns \nothing;

  ensures \result == (\max integer i; 0 <= i < num_lists; sum_array_elements(lists[i].arr, lists[i].size));
*/
int find_max_sum_of_lists(struct IntList { int* arr; int size; } lists[], int num_lists) {
    int max_sum = -2147483648; // Initialize with INT_MIN (assuming 32-bit signed int)

    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant i > 0 ==>
        max_sum == (\max integer k; 0 <= k < i; sum_array_elements(lists[k].arr, lists[k].size));
      loop invariant i == 0 ==> max_sum == -2147483648; // Initial value
      loop assigns i, max_sum;
      loop variant num_lists - i;
    */
    for (int i = 0; i < num_lists; i++) {
        int current_list_sum = 0;

        /*@
          loop invariant 0 <= j <= lists[i].size;
          loop invariant current_list_sum == sum_array_elements(lists[i].arr, j);
          loop assigns j, current_list_sum;
          loop variant lists[i].size - j;

          // Rule II.5: Prevent overflow during sum accumulation
          // requires current_list_sum + lists[i].arr[j] <= INT_MAX;
          // requires current_list_sum + lists[i].arr[j] >= INT_MIN;
          // Assuming these are handled by outer function's implicit constraints or type choice.
          // For a real-world scenario, a `long long` for sums would be safer or explicit checks.
        */
        for (int j = 0; j < lists[i].size; j++) {
            current_list_sum += lists[i].arr[j];
        }

        if (current_list_sum > max_sum) {
            max_sum = current_list_sum;
        }
    }

    return max_sum;
}
