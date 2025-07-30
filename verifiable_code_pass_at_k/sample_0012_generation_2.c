// Task ID: 12
// Generation: 2

/*@
  // Rule II.1: Define recursive logic for sum of a row.
  axiomatic RowSum {
    logic integer row_sum_logic{L}(int* row, int cols);

    axiom row_sum_base{L}:
      \forall int* row, int cols;
        cols == 0 ==> row_sum_logic(row, cols) == 0;

    axiom row_sum_recursive{L}:
      \forall int* row, int cols;
        cols > 0 ==> row_sum_logic(row, cols) == row[cols-1] + row_sum_logic(row, cols-1);

    // Rule II.2: Helper axiom for row_sum_logic to relate to concrete array values.
    // This helps WP connect the logic function to the actual array elements.
    // This axiom effectively says that row_sum_logic(row, cols) is the sum of row[0]...row[cols-1].
    axiom row_sum_concrete_positive{L}:
      \forall int* row, int cols;
        cols > 0 ==> row_sum_logic(row, cols) == \sum(0, cols-1, \lambda integer k; row[k]);
  }
*/

/*@
  requires rows > 0;
  requires cols > 0;

  // Rule II.5: Prevent overflow in sum calculations.
  // Assuming int elements are within typical range [-2^31, 2^31-1].
  // Max possible sum for a row: cols * INT_MAX.
  // INT_MAX is about 2 * 10^9. If cols is 1000, sum could be 2 * 10^12, which overflows int.
  // So, we need to constrain cols based on INT_MAX / max_element_value.
  // For simplicity and to ensure verifiability for typical problem constraints,
  // let's assume elements are non-negative and small enough.
  // If max element is 1000, and max cols is 1000, sum is 10^6, which fits in int.
  // Let's assume elements are small enough such that cols * max_element does not overflow int.
  // A tighter bound would be `requires \forall int r_idx; 0 <= r_idx < rows ==> row_sum_logic(matrix[r_idx], cols) <= INT_MAX;`
  // but row_sum_logic is not directly available in requires as it's defined in axiomatic.
  // We can approximate by constraining `cols` and `matrix[r][c]` values.
  requires cols <= 2000; // Example constraint to keep sum within int range if elements are small (e.g., up to 10^6 / 2000 = 500)
  requires \forall integer r_idx, c_idx; 0 <= r_idx < rows && 0 <= c_idx < cols ==> matrix[r_idx][c_idx] >= 0; // Assume non-negative for simpler sum overflow reasoning
  requires \forall integer r_idx, c_idx; 0 <= r_idx < rows && 0 <= c_idx < cols ==> matrix[r_idx][c_idx] <= 500; // Example constraint

  assigns matrix[0..rows-1][0..cols-1];

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures \forall integer r; 0 <= r < rows - 1 ==>
    row_sum_logic(matrix[r], cols) <= row_sum_logic(matrix[r+1], cols);
  // Ensures that the final matrix contains a permutation of the initial matrix rows.
  ensures \forall integer r_final; 0 <= r_final < rows ==>
    \exists integer r_initial; 0 <= r_initial < rows &&
    \forall integer c; 0 <= c < cols ==> matrix[r_final][c] == \old(matrix[r_initial][c]);
  ensures \forall integer r_initial; 0 <= r_initial < rows ==>
    \exists integer r_final; 0 <= r_final < rows &&
    \forall integer c; 0 <= c < cols ==> matrix[r_final][c] == \old(matrix[r_initial][c]);
*/
void sort_matrix_by_row_sum(int matrix[][100], int rows, int cols) { // Rule I.3: matrix[][100] decays to int (*)[100]
    // Rule I.2: Use int for boolean-like flags if needed, but not directly here.

    // A temporary array to store row sums.
    // This is not part of the problem description, but necessary for the algorithm.
    // Frama-C needs to know its size and properties.
    /*@
      // Requires to ensure `sums` array allocation is safe.
      requires rows <= 1000; // Max rows for `sums` array.
      assigns \nothing; // This block only declares/initializes, no side effects yet.
    */
    int sums[rows]; // VLA, size determined at runtime. Frama-C supports VLAs.

    // Calculate initial row sums
    /*@
      loop invariant 0 <= i <= rows;
      loop invariant \forall integer k; 0 <= k < i ==> sums[k] == row_sum_logic(matrix[k], cols);
      loop assigns i, sums[0..rows-1];
      loop variant rows - i;
    */
    for (int i = 0; i < rows; i++) {
        sums[i] = 0;
        /*@
          loop invariant 0 <= j <= cols;
          loop invariant sums[i] == \sum(0, j-1, \lambda integer k; matrix[i][k]);
          loop assigns j, sums[i];
          loop variant cols - j;
        */
        for (int j = 0; j < cols; j++) {
            // Rule II.5: Prevent overflow during sum accumulation.
            // This requires sums[i] + matrix[i][j] not to overflow.
            // Given the constraints in the function's requires clause (matrix elements <= 500, cols <= 2000),
            // max sum is 2000 * 500 = 1,000,000, which fits in int.
            // So, explicit check here is not strictly needed if outer requires are strong enough.
            sums[i] += matrix[i][j];
        }
    }

    // Bubble sort rows based on their sums
    /*@
      loop invariant 0 <= i <= rows;
      // Invariant: Rows from i to rows-1 are already sorted among themselves based on sum.
      loop invariant \forall integer r1, r2; i <= r1 < r2 < rows ==> sums[r1] <= sums[r2];
      // Invariant: The first 'i' elements are the 'i' smallest elements and are in their final sorted positions.
      loop invariant \forall integer r1; 0 <= r1 < i ==>
        \forall integer r2; i <= r2 < rows ==> sums[r1] <= sums[r2];
      // Invariant: `sums` array elements correctly reflect `row_sum_logic` for the current matrix state.
      loop invariant \forall integer k; 0 <= k < rows ==> sums[k] == row_sum_logic(matrix[k], cols);
      // Invariant for permutation: all elements are still a permutation of the original.
      loop invariant \forall integer r_curr; 0 <= r_curr < rows ==>
        \exists integer r_old; 0 <= r_old < rows &&
        \forall integer c; 0 <= c < cols ==> matrix[r_curr][c] == \at(\old(matrix[r_old][c]), Pre);
      loop invariant \forall integer r_old; 0 <= r_old < rows ==>
        \exists integer r_curr; 0 <= r_curr < rows &&
        \forall integer c; 0 <= c < cols ==> matrix[r_curr][c] == \at(\old(matrix[r_old][c]), Pre);

      loop assigns i, j, sums[0..rows-1], matrix[0..rows-1][0..cols-1];
      loop variant rows - i;
    */
    for (int i = 0; i < rows - 1; i++) {
        /*@
          loop invariant i < j <= rows;
          // Invariant: The `j-1`th element is the maximum among `i` to `j-1`.
          loop invariant \forall integer k; i <= k < j-1 ==> sums[k] <= sums[j-1];
          // Invariant: `sums` array elements correctly reflect `row_sum_logic`.
          loop invariant \forall integer k; 0 <= k < rows ==> sums[k] == row_sum_logic(matrix[k], cols);
          // Invariant for permutation (within inner loop context)
          loop invariant \forall integer r_curr; 0 <= r_curr < rows ==>
            \exists integer r_old; 0 <= r_old < rows &&
            \forall integer c; 0 <= c < cols ==> matrix[r_curr][c] == \at(\old(matrix[r_old][c]), Pre);
          loop invariant \forall integer r_old; 0 <= r_old < rows ==>
            \exists integer r_curr; 0 <= r_curr < rows &&
            \forall integer c; 0 <= c < cols ==> matrix[r_curr][c] == \at(\old(matrix[r_old][c]), Pre);

          loop assigns j, sums[0..rows-1], matrix[0..rows-1][0..cols-1];
          loop variant rows - j;
        */
        for (int j = i + 1; j < rows; j++) {
            if (sums[i] > sums[j]) {
                // Swap sums
                int temp_sum = sums[i];
                sums[i] = sums[j];
                sums[j] = temp_sum;

                // Swap rows in the matrix
                /*@
                  loop invariant 0 <= k <= cols;
                  loop invariant \forall integer l; 0 <= l < k ==> matrix[i][l] == \at(matrix[j][l], Pre) && matrix[j][l] == \at(matrix[i][l], Pre);
                  loop assigns k, matrix[i][0..cols-1], matrix[j][0..cols-1];
                  loop variant cols - k;
                */
                for (int k = 0; k < cols; k++) {
                    int temp_val = matrix[i][k];
                    matrix[i][k] = matrix[j][k];
                    matrix[j][k] = temp_val;
                }
            }
        }
    }
}
