// Task ID: 12
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic RowSum {
    logic integer row_sum_val{L}(int* row, integer cols);

    axiom row_sum_base{L}:
      \forall int* row, integer cols;
      cols == 0 ==> row_sum_val(row, cols) == 0;

    axiom row_sum_recursive{L}:
      \forall int* row, integer cols;
      cols > 0 ==> row_sum_val(row, cols) == row[cols - 1] + row_sum_val(row, cols - 1);

    // Helper axiom: if all elements are positive, sum is positive
    axiom row_sum_positive{L}:
      \forall int* row, integer cols;
      (\forall integer k; 0 <= k < cols ==> row[k] >= 0) ==> row_sum_val(row, cols) >= 0;

    // Helper axiom: if all elements are within a range, sum is within a derived range
    // Requires: -1000 <= row[k] <= 1000 for simplicity
    axiom row_sum_range{L}:
      \forall int* row, integer cols;
      (cols > 0 && \forall integer k; 0 <= k < cols ==> -1000 <= row[k] <= 1000) ==>
      -1000 * cols <= row_sum_val(row, cols) <= 1000 * cols;
  }
*/

/*@
  requires rows > 0;
  requires cols > 0;
  // Rule II.5: Prevent potential overflow during sum calculation, assuming matrix elements are int and within reasonable bounds.
  // Max possible sum for a row: 1000 * cols. Max int is 2*10^9. So 1000 * cols < 2*10^9 implies cols < 2*10^6.
  // For safety, let's assume a practical limit on cols to prevent overflow in row_sum_val.
  requires cols <= 100000; // Adjust based on expected element range and int max.
  
  // Ensures the matrix is sorted by row sums.
  // Rule I.3: Array pointer decay, so matrix[i] is int*
  ensures \forall integer i; 0 <= i < rows - 1 ==> row_sum_val(matrix[i], cols) <= row_sum_val(matrix[i+1], cols);

  // Behavior of assigns: the entire matrix might be modified.
  assigns matrix[0..rows-1][0..cols-1];
*/
void sort_matrix_by_row_sum(int matrix[][100], int rows, int cols) { // Rule I.3: matrix[][100] decays to int (*matrix)[100]
    // Rule II.4: Mandatory loop annotations.
    /*@
      loop invariant 0 <= i && i <= rows;
      loop invariant \forall integer k; 0 <= k < i ==>
        \forall integer l; k < l < rows ==> row_sum_val(matrix[k], cols) <= row_sum_val(matrix[l], cols);
      loop assigns i, j, matrix[0..rows-1][0..cols-1];
      loop variant rows - i;
    */
    for (int i = 0; i < rows - 1; i++) {
        /*@
          loop invariant i <= j && j <= rows;
          loop invariant \forall integer k; i <= k < j ==>
            row_sum_val(matrix[i], cols) <= row_sum_val(matrix[k], cols);
          loop invariant \forall integer k; i <= k < j ==>
            \forall integer l; j <= l < rows ==> row_sum_val(matrix[k], cols) <= row_sum_val(matrix[l], cols);
          loop assigns j, matrix[0..rows-1][0..cols-1];
          loop variant rows - j;
        */
        for (int j = i + 1; j < rows; j++) {
            // Rule II.5: Prevent overflow if row_sum_val can be very large.
            // This is implicitly handled by the requires clause on `cols` for the function.
            if (row_sum_val(matrix[i], cols) > row_sum_val(matrix[j], cols)) {
                // Swap rows
                /*@
                  loop invariant 0 <= k && k <= cols;
                  loop assigns matrix[i][0..cols-1], matrix[j][0..cols-1], k;
                  loop variant cols - k;
                */
                for (int k = 0; k < cols; k++) {
                    int temp = matrix[i][k];
                    matrix[i][k] = matrix[j][k];
                    matrix[j][k] = temp;
                }
            }
        }
    }
}
