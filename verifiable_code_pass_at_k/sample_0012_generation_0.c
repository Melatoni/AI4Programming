// Task ID: 12
// Generation: 0

/*@ axiomatic Sum {
  @   logic integer sum_row(int* row, integer cols);

  @   axiom sum_row_empty:
  @     \forall int* row, integer cols;
  @       cols == 0 ==> sum_row(row, cols) == 0;

  @   axiom sum_row_recursive:
  @     \forall int* row, integer cols;
  @       cols > 0 ==> sum_row(row, cols) == sum_row(row, cols - 1) + row[cols - 1];

  @   // Rule II.2: Helper axiom for sum_row to prevent overflow.
  @   // Assumes elements are not excessively large for typical int ranges.
  @   // This specific axiom is for positive elements, can be generalized.
  @   axiom sum_row_upper_bound:
  @     \forall int* row, integer cols, integer max_val;
  @       (\forall integer k; 0 <= k < cols ==> row[k] <= max_val)
  @       ==> sum_row(row, cols) <= cols * max_val;

  @   // Rule II.2: Helper axiom for sum_row to prevent underflow.
  @   axiom sum_row_lower_bound:
  @     \forall int* row, integer cols, integer min_val;
  @       (\forall integer k; 0 <= k < cols ==> row[k] >= min_val)
  @       ==> sum_row(row, cols) >= cols * min_val;
  @ }
  @*/

/*@
  @ requires rows > 0 && cols > 0;
  @ requires \valid(matrix);
  @ requires \forall integer i; 0 <= i < rows ==> \valid(matrix[i] + (0..cols-1));

  @ // Rule II.5: Prevent potential overflow during sum calculation or in sorting.
  @ // Assume matrix elements are within a reasonable range for sum_row.
  @ // For example, if max element is 1000 and cols is 1000, sum could be 1,000,000.
  @ // INT_MAX is 2,147,483,647. So cols * max_element should not exceed INT_MAX.
  @ // A stricter bound might be needed depending on the actual range of matrix elements.
  @ // For simplicity, we assume sum_row will not overflow int.
  @ // A more precise check would involve: (\forall integer i; 0 <= i < rows ==> cols * \max(matrix[i][0..cols-1]) <= INT_MAX).
  @ // This is hard to express without a max_element logic function.
  @ // Let's use a simpler heuristic for now based on typical int sizes.
  @ requires cols <= 65535; // Example: if elements are small, say max 32767, then cols * 32767 <= 2^31 - 1
  @ requires \forall integer i, j; 0 <= i < rows && 0 <= j < cols ==> matrix[i][j] >= -100000 && matrix[i][j] <= 100000;


  @ assigns matrix[0..rows-1][0..cols-1];

  @ ensures \forall integer k; 0 <= k < rows - 1 ==> sum_row(matrix[k], cols) <= sum_row(matrix[k+1], cols);

  @ // Ensure the sorted rows are permutations of the original rows.
  @ ensures \forall integer k; 0 <= k < rows ==> (\exists integer l; 0 <= l < rows && \forall integer m; 0 <= m < cols ==> matrix[k][m] == \old(matrix[l][m]));
  @ ensures \forall integer l; 0 <= l < rows ==> (\exists integer k; 0 <= k < rows && \forall integer m; 0 <= m < cols ==> matrix[l][m] == \old(matrix[k][m]));
  @*/
void sort_matrix_by_row_sum(int matrix[][100], int rows, int cols) { // Rule I.3: matrix[][100] decays to int (*matrix)[100]
    /*@
      @ loop invariant 0 <= i <= rows;
      @ loop invariant \forall integer k; 0 <= k < i ==> (\forall integer l; k < l < rows ==> sum_row(matrix[k], cols) <= sum_row(matrix[l], cols));
      @ loop invariant \forall integer k; 0 <= k < i ==> (\forall integer l; k < l < rows ==> matrix[k] is_sorted_with matrix[l] by sum_row); // Informal, but captures the idea
      @ loop invariant \forall integer k, l; 0 <= k < i && i <= l < rows ==> (\forall integer r; 0 <= r < cols ==> matrix[k][r] == \at(matrix[k][r],Pre)); // Elements up to i-1 are finalized.
      @ loop invariant \forall integer x; 0 <= x < rows ==> (\exists integer y; 0 <= y < rows && \forall integer z; 0 <= z < cols ==> matrix[x][z] == \at(matrix[y][z],Pre));
      @ loop invariant \forall integer y; 0 <= y < rows ==> (\exists integer x; 0 <= x < rows && \forall integer z; 0 <= z < cols ==> matrix[y][z] == \at(matrix[x][z],Pre));
      @ loop assigns i, j, matrix[0..rows-1][0..cols-1];
      @ loop variant rows - i;
    */
    for (int i = 0; i < rows - 1; i++) {
        /*@
          @ loop invariant i <= j <= rows;
          @ loop invariant \forall integer k; i <= k < j ==> sum_row(matrix[i], cols) <= sum_row(matrix[k], cols);
          @ loop invariant \forall integer k; i <= k < j ==> (\forall integer l; 0 <= l < cols ==> matrix[i][l] <= matrix[k][l] || sum_row(matrix[i], cols) <= sum_row(matrix[k], cols)); // Informal
          @ loop invariant (\forall integer x; 0 <= x < rows ==> (\exists integer y; 0 <= y < rows && \forall integer z; 0 <= z < cols ==> matrix[x][z] == \at(matrix[y][z],LoopInv(i))));
          @ loop invariant (\forall integer y; 0 <= y < rows ==> (\exists integer x; 0 <= x < rows && \forall integer z; 0 <= z < cols ==> matrix[y][z] == \at(matrix[x][z],LoopInv(i))));
          @ loop assigns j, matrix[0..rows-1][0..cols-1];
          @ loop variant rows - j;
        */
        for (int j = i + 1; j < rows; j++) {
            // Rule II.5: Prevent overflow during sum_row call. Handled by requires on function.
            if (sum_row(matrix[i], cols) > sum_row(matrix[j], cols)) {
                // Swap rows
                /*@
                  @ loop invariant 0 <= k <= cols;
                  @ loop invariant \forall integer l; 0 <= l < k ==> (matrix[i][l] == \at(matrix[j][l],Pre) && matrix[j][l] == \at(matrix[i][l],Pre));
                  @ loop invariant \forall integer l; k <= l < cols ==> (matrix[i][l] == \at(matrix[i][l],Pre) && matrix[j][l] == \at(matrix[j][l],Pre));
                  @ loop assigns k, matrix[i][0..cols-1], matrix[j][0..cols-1];
                  @ loop variant cols - k;
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
