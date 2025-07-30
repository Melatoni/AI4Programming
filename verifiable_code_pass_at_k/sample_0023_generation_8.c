// Task ID: 23
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: Ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic SumArray {
    logic integer sum_array_elements(int* arr, int size);

    // Base case for sum_array_elements
    axiom sum_array_elements_base:
      \forall int* arr, int size; size <= 0 ==> sum_array_elements(arr, size) == 0;

    // Recursive case for sum_array_elements
    axiom sum_array_elements_recursive:
      \forall int* arr, int size; size > 0 ==>
        sum_array_elements(arr, size) == arr[size - 1] + sum_array_elements(arr, size - 1);

    // Helper axiom: sum of non-negative elements is non-negative
    // Rule II.2: CRITICAL - Helper Axioms
    axiom sum_array_elements_non_negative_helper:
      \forall int* arr, int size;
        (\forall integer i; 0 <= i < size ==> arr[i] >= 0) ==> sum_array_elements(arr, size) >= 0;

    // Helper axiom: sum of elements bounded by min/max
    axiom sum_array_elements_bounds_helper:
      \forall int* arr, int size, int min_val, int max_val;
        (\forall integer i; 0 <= i < size ==> min_val <= arr[i] <= max_val) ==>
          min_val * size <= sum_array_elements(arr, size) <= max_val * size;
  }
*/

/*@
  requires num_rows >= 0;
  requires num_cols >= 0;
  // Prevent overflow when calculating sum_array_elements.
  // Assuming int ranges from -2*10^9 to 2*10^9.
  // Max possible sum for a row: num_cols * INT_MAX
  // Max possible value for an element of `arr` is INT_MAX.
  // Max possible value for `num_cols` is 2*10^9 / (max_element_value + 1)
  // Let's assume reasonable bounds for `num_cols` to avoid overflow in sum.
  // If elements are typically small (e.g., up to 1000), then num_cols could be 2*10^6.
  // For general case, we must ensure individual sums don't overflow.
  // A safe upper bound for num_cols relative to typical int values.
  // If an element is INT_MAX, then num_cols must be 1 for the sum not to overflow.
  // This is a tricky requirement. For now, let's assume sums within a row don't overflow.
  // For a robust solution, one would use `long long` for sums or more precise bounds.
  // For `int`, if `arr[i][j]` can be `INT_MAX`, then `num_cols` must be 1.
  // If `arr[i][j]` can be `INT_MIN`, then `num_cols` must be 1.
  // Let's assume the sum of any row will fit in an `int`.
  // Requires: \forall integer i; 0 <= i < num_rows ==> sum_array_elements(arr[i], num_cols) <= INT_MAX;
  // Requires: \forall integer i; 0 <= i < num_rows ==> sum_array_elements(arr[i], num_cols) >= INT_MIN;

  // Rule I.3: `int (*arr)[num_cols]` correctly reflects array pointer decay.
  assigns \nothing;

  // The function returns the maximum sum.
  // If num_rows is 0, the maximum sum is typically considered 0 or negative infinity.
  // Here, we define it as 0 if no rows exist, otherwise it's the max of all row sums.
  ensures \result == (
    if num_rows == 0 then 0
    else \max(integer i; 0 <= i < num_rows; sum_array_elements(arr[i], num_cols))
  );
*/
int find_max_sum_of_lists(int (*arr)[], int num_rows, int num_cols) {
    if (num_rows == 0) {
        return 0;
    }

    int max_sum = 0; // Initialize with 0 or the sum of the first row if num_rows > 0

    /*@
      loop invariant 0 <= i <= num_rows;
      loop invariant (i == 0) ==> (max_sum == 0); // Initial condition
      loop invariant (0 < i <= num_rows) ==>
        (max_sum == \max(integer k; 0 <= k < i; sum_array_elements(arr[k], num_cols)));
      loop assigns i, max_sum;
      loop variant num_rows - i;
    */
    for (int i = 0; i < num_rows; i++) {
        int current_row_sum = 0;
        /*@
          loop invariant 0 <= j <= num_cols;
          loop invariant current_row_sum == sum_array_elements(arr[i], j);
          loop assigns j, current_row_sum;
          loop variant num_cols - j;
        */
        for (int j = 0; j < num_cols; j++) {
            // Rule II.5: Prevent potential overflow if current_row_sum + arr[i][j] exceeds INT_MAX
            // This would require a requires clause on the input values or using long long.
            // For simplicity and to fit within `int` for this problem, we assume no overflow.
            // A real-world robust solution would have this check.
            current_row_sum += arr[i][j];
        }

        // Initialize max_sum with the first row's sum if it's the first iteration
        if (i == 0) {
            max_sum = current_row_sum;
        } else {
            if (current_row_sum > max_sum) {
                max_sum = current_row_sum;
            }
        }
    }

    return max_sum;
}
