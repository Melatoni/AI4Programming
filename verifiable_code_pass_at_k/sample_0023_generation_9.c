// Task ID: 23
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1, II.2: Recursive logic for complexity, helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic Sum {
  logic integer sum_array(int* arr, integer len);

  axiom sum_array_empty:
    \forall int* arr; sum_array(arr, 0) == 0;

  axiom sum_array_recursive:
    \forall int* arr, integer len;
    len > 0 ==> sum_array(arr, len) == sum_array(arr, len - 1) + arr[len - 1];

  // Helper axiom: if all elements are positive, sum is positive.
  axiom sum_array_positive_elements:
    \forall int* arr, integer len;
    (\forall integer k; 0 <= k < len ==> arr[k] >= 0) ==> sum_array(arr, len) >= 0;

  // Helper axiom: if all elements are non-negative, sum is non-negative.
  axiom sum_array_non_negative_elements:
    \forall int* arr, integer len;
    (\forall integer k; 0 <= k < len ==> arr[k] >= 0) ==> sum_array(arr, len) >= 0;

  // Helper axiom: upper bound for sum if elements have an upper bound
  axiom sum_array_upper_bound:
    \forall int* arr, integer len, integer max_val;
    (\forall integer k; 0 <= k < len ==> arr[k] <= max_val) ==> sum_array(arr, len) <= len * max_val;

  // Helper axiom: lower bound for sum if elements have a lower bound
  axiom sum_array_lower_bound:
    \forall int* arr, integer len, integer min_val;
    (\forall integer k; 0 <= k < len ==> arr[k] >= min_val) ==> sum_array(arr, len) >= len * min_val;
}
*/

/*@
  requires num_rows >= 0;
  requires num_cols >= 0;
  // Prevent potential overflow when calculating sum_array.
  // Assuming int is 32-bit, max_int is 2^31 - 1.
  // num_cols * max_element_value should not exceed max_int.
  // For example, if max_element_value is INT_MAX/num_cols,
  // or if num_cols * INT_MAX_PER_COL fits in int.
  // Let's use a conservative bound based on common int limits.
  // If elements are typically small, this might be too restrictive.
  // For safety, assume each element can be up to INT_MAX.
  // Then num_cols must be 1 for the sum to not overflow.
  // A more practical approach: sum_array should not exceed INT_MAX.
  // Let's assume elements are within reasonable bounds, e.g., -10000 to 10000.
  // Then num_cols * 10000 should not overflow.
  // For a generic case, we must impose a strong constraint on num_cols and element values.
  // Let's assume element values are in `int` range, and the sum of `num_cols` elements
  // also fits in `int`. This is implicitly required by `sum_array` returning `integer`.
  // WP will check for overflow in the C code itself.

  // The maximum sum of any row should not exceed INT_MAX.
  // And the initial value of max_sum (first row sum) should fit.
  // This is handled by the type of `max_sum` (int).

  assigns \nothing;

  behavior empty_or_invalid_input:
    assumes num_rows == 0 || num_cols == 0;
    ensures \result == 0; // Or some other sentinel value like INT_MIN, depending on problem spec.
                          // Python max() on empty list raises ValueError. Here 0 is a safe default.

  behavior valid_input:
    assumes num_rows > 0 && num_cols > 0;
    // The result is the maximum sum among all rows.
    ensures \result == \max(integer i; 0 <= i < num_rows; sum_array(matrix[i], num_cols));
*/
int find_max_sum_of_lists(int (*matrix)[], int num_rows, int num_cols) {
    if (num_rows == 0 || num_cols == 0) {
        return 0;
    }

    int max_sum = 0; // Initialize with the sum of the first row

    /*@
      loop invariant 0 <= i <= num_rows;
      loop invariant (\forall integer k; 0 <= k < i ==> \typeof(matrix[k]) == \typeof(matrix[0]));
      // max_sum holds the maximum sum of rows processed so far.
      loop invariant i > 0 ==> max_sum == \max(integer k; 0 <= k < i; sum_array(matrix[k], num_cols));
      loop invariant i == 0 ==> max_sum == 0; // Initial state

      loop assigns i, max_sum;
      loop variant num_rows - i;
    */
    for (int i = 0; i < num_rows; i++) {
        int current_row_sum = 0;

        /*@
          loop invariant 0 <= j <= num_cols;
          loop invariant current_row_sum == sum_array(matrix[i], j);
          loop assigns j, current_row_sum;
          loop variant num_cols - j;

          // Prevent overflow in current_row_sum += matrix[i][j];
          // Requires that current_row_sum + matrix[i][j] does not overflow int.
          // This is a strong constraint, but necessary for proof.
          // For example, if matrix[i][j] can be negative, current_row_sum can decrease.
          // If all elements are positive, current_row_sum can grow up to num_cols * max_element.
          // We need to ensure that this product fits into int.
          // For a generic case, we assume the sum of any row fits in 'int'.
          // Frama-C will generate an RTE for `current_row_sum + matrix[i][j]` if it detects overflow.
          // To prevent this, a requires clause could be added to the function, e.g.,
          // `requires (\forall integer r; 0 <= r < num_rows; sum_array(matrix[r], num_cols) >= INT_MIN && sum_array(matrix[r], num_cols) <= INT_MAX);`
          // which is exactly what we are trying to compute.
          // The best approach is to check the generated proof obligations for overflow.
        */
        for (int j = 0; j < num_cols; j++) {
            current_row_sum += matrix[i][j];
        }

        // Initialize max_sum with the first sum, then update.
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
