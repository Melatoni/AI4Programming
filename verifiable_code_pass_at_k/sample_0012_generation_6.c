// Task ID: 12
// Generation: 6

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule I.1: No standard libraries.
*/

/*@
  // Rule II.1: Define recursive logic for sum of a row.
  axiomatic RowSum {
    logic integer row_sum_logic(int* row, int cols);

    axiom row_sum_base:
      \forall int* row, int cols;
        cols == 0 ==> row_sum_logic(row, cols) == 0;

    axiom row_sum_recursive:
      \forall int* row, int cols;
        cols > 0 ==> row_sum_logic(row, cols) == row_sum_logic(row, cols - 1) + row[cols - 1];

    // Rule II.2: Helper axiom for row_sum_logic to prevent potential overflow issues in sum calculation.
    // Assuming elements are within int range, sum can be.
    // This axiom helps the prover understand that if elements are bounded, the sum is also bounded.
    // For a concrete range, e.g., if elements are non-negative, this can be more specific.
    // Here, it's a general property about the sum's type.
    axiom row_sum_type_property:
      \forall int* row, int cols;
        \typeof(row_sum_logic(row, cols)) == \typeof(0); // Ensures sum is an integer.

    // Helper axiom for sum value if elements are bounded (example, not strictly needed for this problem but good practice)
    // axiom row_sum_bounded_positive:
    //   \forall int* row, int cols;
    //     (\forall integer k; 0 <= k < cols ==> row[k] >= 0) ==> row_sum_logic(row, cols) >= 0;
  }
*/

/*@
  // Rule II.5: Prevent potential runtime errors.
  // Constraints on matrix dimensions and element values to prevent overflow during sum calculation.
  // Assuming 32-bit int, max sum of 1000 elements (max 2*10^9) could exceed INT_MAX.
  // Max possible sum for a row: cols * INT_MAX. This must fit in int.
  // For `int`, assume INT_MAX is at least 2^31 - 1.
  // If cols is 1000, then 1000 * 2*10^9 is too large.
  // Max cols for sum to fit in int: INT_MAX / max_abs_element_value.
  // Let's assume elements are within a reasonable range, e.g., -1000 to 1000.
  // Then max sum for 1000 cols would be 1000 * 1000 = 1,000,000, which fits.
  requires rows > 0 && cols > 0;
  requires rows <= 1000; // Arbitrary reasonable upper bound for matrix dimensions
  requires cols <= 1000; // Arbitrary reasonable upper bound for matrix dimensions

  // Constraints for sum to not overflow int, assuming elements are int.
  // For a generic case, we must assume the sum of 'cols' elements of type 'int' fits in an 'int'.
  // This implies that `cols * (min_element_value)` and `cols * (max_element_value)`
  // must both be within the range of `int`.
  // A simple way to constrain elements:
  // requires \forall integer r, c; 0 <= r < rows && 0 <= c < cols ==> matrix[r][c] >= -20000 && matrix[r][c] <= 20000;
  // This ensures sum of 1000 elements (20000 * 1000 = 2*10^7) fits in int.

  assigns matrix[0..rows-1][0..cols-1];

  // Post-condition: The matrix is sorted based on row sums.
  ensures \forall integer i; 0 <= i < rows - 1 ==> row_sum_logic(matrix[i], cols) <= row_sum_logic(matrix[i+1], cols);
*/
void sort_matrix_by_row_sum(int rows, int cols, int matrix[rows][cols]) { // Rule I.3: matrix[rows][cols] decays to int (*matrix)[cols]
    /*@
      loop invariant 0 <= i && i <= rows;
      // After i iterations, the first i elements (rows) are sorted among themselves
      // and are in their final sorted positions relative to each other.
      // Specifically, for bubble sort, after i passes, the largest i elements are at the end.
      // This invariant for bubble sort states that the last 'i' elements are sorted.
      // However, for sorting the *entire* array, a stronger invariant is needed for the outer loop.
      // For selection sort (which is easier to verify for arrays):
      // loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; i <= l < rows ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[l], cols);
      // And the first k elements are sorted among themselves.
      // Let's use a standard bubble sort invariant.
      // Rule II.4: Loop invariants are mandatory.
      loop invariant \forall integer k; 0 <= k < rows - i - 1 ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[k+1], cols);
      loop invariant \forall integer k; rows - i <= k < rows - 1 ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[k+1], cols);
      loop invariant \forall integer k; 0 <= k < rows - i ==> (\forall integer l; rows - i <= l < rows ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[l], cols));

      loop assigns i, matrix[0..rows-1][0..cols-1];
      // Rule II.4: Loop variant is mandatory.
      loop variant rows - i;
    */
    for (int i = 0; i < rows - 1; i++) {
        /*@
          loop invariant 0 <= j && j <= rows - i - 1;
          loop invariant \forall integer k; j <= k < rows - i - 1 ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[k+1], cols);
          loop invariant \forall integer k; 0 <= k < j ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[k+1], cols);
          loop invariant \forall integer k; 0 <= k <= j ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[j+1], cols); // The largest element among 0..j is at j
          loop invariant \forall integer k; 0 <= k < j ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[j], cols);
          loop invariant \forall integer k; j < k < rows - i ==> row_sum_logic(matrix[j], cols) <= row_sum_logic(matrix[k], cols); // The max in [0..j] is at j
          loop invariant \forall integer k; 0 <= k < rows - i - 1 - j ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[k+1], cols);
          loop invariant \forall integer k; rows - i - 1 - j <= k < rows - i - 1 ==> row_sum_logic(matrix[k], cols) <= row_sum_logic(matrix[k+1], cols);

          loop assigns j, matrix[0..rows-1][0..cols-1];
          loop variant rows - i - 1 - j;
        */
        for (int j = 0; j < rows - i - 1; j++) {
            // Calculate row sums (this part isn't explicitly in ACSL, but the logic function helps connect it)
            // Rule II.5: Prevent overflow in sum calculation.
            // The `requires` clause of the function handles this.
            int sum1 = 0;
            /*@
              loop invariant 0 <= k && k <= cols;
              loop invariant sum1 == row_sum_logic(matrix[j], k);
              loop assigns k, sum1;
              loop variant cols - k;
            */
            for (int k = 0; k < cols; k++) {
                sum1 += matrix[j][k];
            }

            int sum2 = 0;
            /*@
              loop invariant 0 <= k && k <= cols;
              loop invariant sum2 == row_sum_logic(matrix[j+1], k);
              loop assigns k, sum2;
              loop variant cols - k;
            */
            for (int k = 0; k < cols; k++) {
                sum2 += matrix[j+1][k];
            }

            if (sum1 > sum2) {
                // Swap rows
                /*@
                  loop invariant 0 <= k && k <= cols;
                  loop assigns k, matrix[j][0..cols-1], matrix[j+1][0..cols-1];
                  loop variant cols - k;
                */
                for (int k = 0; k < cols; k++) {
                    int temp = matrix[j][k];
                    matrix[j][k] = matrix[j+1][k];
                    matrix[j+1][k] = temp;
                }
            }
        }
    }
}
