// Task ID: 12
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity (summation).
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic RowSum {
    logic integer row_sum_recursive{L}(int* row, integer col_idx, integer num_cols) =
      if col_idx >= num_cols then
        0
      else
        row[col_idx] + row_sum_recursive{L}(row, col_idx + 1, num_cols);

    // Helper axiom: sum of empty row is 0.
    axiom row_sum_empty{L}:
      \forall int* row, integer num_cols;
      row_sum_recursive{L}(row, num_cols, num_cols) == 0;

    // Helper axiom: sum of a single element row.
    axiom row_sum_single{L}:
      \forall int* row, integer col_idx, integer num_cols;
      col_idx < num_cols ==>
      row_sum_recursive{L}(row, col_idx, num_cols) == row[col_idx] + row_sum_recursive{L}(row, col_idx + 1, num_cols);

    // A more direct logic function for row sum, often easier for provers.
    logic integer row_sum{L}(int* row, integer num_cols) =
      row_sum_recursive{L}(row, 0, num_cols);

    // Helper axiom: sum of elements within a range.
    // Proves that if all elements are non-negative, the sum is non-negative.
    axiom row_sum_non_negative{L}:
      \forall int* row, integer num_cols;
      (\forall integer j; 0 <= j < num_cols ==> row[j] >= 0) ==>
      row_sum{L}(row, num_cols) >= 0;

    // Helper axiom: sum of elements within a range (upper bound).
    // Proves that if all elements are <= M, sum <= num_cols * M.
    axiom row_sum_upper_bound{L}:
      \forall int* row, integer num_cols, integer M;
      (\forall integer j; 0 <= j < num_cols ==> row[j] <= M) ==>
      row_sum{L}(row, num_cols) <= num_cols * M;

    // Helper axiom: sum of elements within a range (lower bound).
    // Proves that if all elements are >= m, sum >= num_cols * m.
    axiom row_sum_lower_bound{L}:
      \forall int* row, integer num_cols, integer m;
      (\forall integer j; 0 <= j < num_cols ==> row[j] >= m) ==>
      row_sum{L}(row, num_cols) >= num_cols * m;
  }
*/

/*@
  // Rule I.3: Array pointer decay. T arr[R][C] becomes T (*arr)[C].
  // Rule II.5: Prevent RTE for matrix dimensions.
  requires num_rows >= 0 && num_cols >= 0;
  requires \valid_read(matrix) && \valid_read(matrix[0..num_rows-1][0..num_cols-1]);
  requires num_rows <= INT_MAX / sizeof(int*); // Prevent overflow on stack allocation if it were dynamic.
  requires num_cols <= INT_MAX / sizeof(int); // Prevent overflow on stack allocation if it were dynamic.

  // The function modifies the matrix.
  assigns matrix[0..num_rows-1][0..num_cols-1];

  // The core post-condition for sorting:
  // 1. All elements are still the same (permutation).
  // 2. Rows are sorted by their sum.
  ensures \forall integer i, j; 0 <= i < num_rows - 1 && 0 <= j < num_rows - 1 ==>
    (row_sum{Old}(matrix[i], num_cols) <= row_sum{Old}(matrix[i+1], num_cols) ==>
     row_sum{Here}(matrix[i], num_cols) <= row_sum{Here}(matrix[i+1], num_cols));
  ensures \forall integer i; 0 <= i < num_rows - 1 ==>
    row_sum{Here}(matrix[i], num_cols) <= row_sum{Here}(matrix[i+1], num_cols);

  // This ensures that the set of rows remains the same, just reordered.
  // This is a strong property for sorting algorithms.
  ensures \forall integer i; 0 <= i < num_rows ==>
    \exists integer j; 0 <= j < num_rows &&
    (\forall integer k; 0 <= k < num_cols ==> matrix[i][k] == \at(matrix[j][k],Old));

*/
void sort_matrix_by_row_sum(int num_rows, int num_cols, int matrix[][num_cols]) {
    /*@
      loop invariant 0 <= i <= num_rows;
      loop invariant \forall integer k; 0 <= k < i ==>
        \forall integer l; k < l < num_rows ==>
          row_sum{Here}(matrix[k], num_cols) <= row_sum{Here}(matrix[l], num_cols);
      loop invariant \forall integer k; 0 <= k < i ==>
        \forall integer l; 0 <= l < k ==>
          row_sum{Here}(matrix[l], num_cols) <= row_sum{Here}(matrix[k], num_cols);

      // Rule II.4: Loop variant for outer loop.
      loop variant num_rows - i;
      loop assigns i, matrix[0..num_rows-1][0..num_cols-1];
    */
    for (int i = 0; i < num_rows - 1; ++i) {
        /*@
          loop invariant i < j <= num_rows;
          loop invariant \forall integer k; i < k < j ==>
            row_sum{Here}(matrix[i], num_cols) <= row_sum{Here}(matrix[k], num_cols);
          loop invariant \forall integer k; i <= k < j ==>
            \forall integer l; k < l < j ==>
              row_sum{Here}(matrix[k], num_cols) <= row_sum{Here}(matrix[l], num_cols);
          loop invariant \forall integer k; i <= k < j ==>
            \forall integer l; j <= l < num_rows ==>
              row_sum{Here}(matrix[k], num_cols) <= row_sum{Here}(matrix[l], num_cols);
          loop invariant \forall integer k; 0 <= k < i ==>
            row_sum{Here}(matrix[k], num_cols) <= row_sum{Here}(matrix[i], num_cols);

          // Rule II.4: Loop variant for inner loop.
          loop variant num_rows - j;
          loop assigns j, matrix[0..num_rows-1][0..num_cols-1];
        */
        for (int j = i + 1; j < num_rows; ++j) {
            // Rule II.5: Prevent overflow in intermediate sum calculations if needed.
            // For row_sum, this is handled by the type of integer.
            if (row_sum(matrix[i], num_cols) > row_sum(matrix[j], num_cols)) {
                // Swap rows
                /*@
                  loop invariant 0 <= k <= num_cols;
                  loop assigns k, matrix[i][0..num_cols-1], matrix[j][0..num_cols-1];
                  loop variant num_cols - k;
                */
                for (int k = 0; k < num_cols; ++k) {
                    int temp = matrix[i][k];
                    matrix[i][k] = matrix[j][k];
                    matrix[j][k] = temp;
                }
            }
        }
    }
}
