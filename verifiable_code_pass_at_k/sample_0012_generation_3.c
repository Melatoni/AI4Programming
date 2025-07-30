// Task ID: 12
// Generation: 3

/*@
  // Axiomatic block for recursive sum function (Rule II.1)
  axiomatic RowSum {
  logic integer sum_row(int* row, integer cols);

  axiom sum_row_base:
  \forall int* row, integer cols;
  cols == 0 ==> sum_row(row, cols) == 0;

  axiom sum_row_recursive:
  \forall int* row, integer cols;
  cols > 0 ==> sum_row(row, cols) == row[cols - 1] + sum_row(row, cols - 1);

  // Helper axiom for sum_row (Rule II.2)
  axiom sum_row_non_negative:
  \forall int* row, integer cols;
  (\forall integer k; 0 <= k < cols ==> row[k] >= 0) ==> sum_row(row, cols) >= 0;
  }
*/

/*@
  // Axiomatic block for properties of sorted rows
  axiomatic SortedRows {
  logic boolean is_sorted_by_row_sum(int** matrix, integer rows, integer cols);

  axiom is_sorted_by_row_sum_base:
  \forall int** matrix, integer rows, integer cols;
  rows <= 1 ==> is_sorted_by_row_sum(matrix, rows, cols);

  axiom is_sorted_by_row_sum_recursive:
  \forall int** matrix, integer rows, integer cols;
  rows > 1 ==> (sum_row(matrix[rows-2], cols) <= sum_row(matrix[rows-1], cols) &&
  is_sorted_by_row_sum(matrix, rows-1, cols));
  }
*/

/*@
  requires rows > 0;
  requires cols > 0;
  requires \valid_read(matrix + (0..rows-1));
  requires \forall integer i; 0 <= i < rows ==> \valid_read(*(matrix + i) + (0..cols-1));
  // Rule II.5: Prevent potential overflow if row sums are large.
  // Assuming int can hold sum of cols elements. For example, if cols=1000, max int is 2*10^9,
  // then max element value should be around 2*10^6.
  // This requires clause is a placeholder; actual bounds depend on int type and `cols`.
  requires \forall integer i, j; 0 <= i < rows && 0 <= j < cols ==> matrix[i][j] >= 0; // Example: assuming non-negative for sum_row_non_negative helper axiom
  requires \forall integer i; 0 <= i < rows ==> sum_row(matrix[i], cols) <= 2000000000; // Example limit for sum

  assigns matrix[0..rows-1][0..cols-1];

  ensures is_sorted_by_row_sum(matrix, rows, cols);
  ensures \forall integer r; 0 <= r < rows ==>
  (\forall integer c; 0 <= c < cols ==>
  \exists integer old_r; 0 <= old_r < \old(rows) &&
  \exists integer old_c; 0 <= old_c < \old(cols) &&
  matrix[r][c] == \old(matrix[old_r][old_c])); // Permutation property
  ensures \forall integer old_r; 0 <= old_r < \old(rows) ==>
  (\forall integer old_c; 0 <= old_c < \old(cols) ==>
  \exists integer r; 0 <= r < rows &&
  \exists integer c; 0 <= c < cols &&
  matrix[r][c] == \old(matrix[old_r][old_c])); // Permutation property
*/
void sort_matrix_by_row_sum(int** matrix, int rows, int cols) {
  /*@
    loop invariant 0 <= i && i <= rows;
    loop invariant \forall integer k; 0 <= k < i ==>
    \forall integer p; k < p < rows ==> sum_row(matrix[k], cols) <= sum_row(matrix[p], cols);
    loop invariant \forall integer k; 0 <= k < i ==>
    (\forall integer p; k <= p < rows ==>
    \exists integer old_r; 0 <= old_r < \old(rows) &&
    \exists integer old_c; 0 <= old_c < \old(cols) &&
    matrix[k][p] == \old(matrix[old_r][old_c])); // Permutation
    loop assigns i, matrix[0..rows-1][0..cols-1];
    loop variant rows - i;
  */
  for (int i = 0; i < rows - 1; i++) {
    /*@
      loop invariant i <= j && j <= rows;
      loop invariant \forall integer k; i <= k < j ==>
      sum_row(matrix[k], cols) >= sum_row(matrix[i], cols);
      loop invariant \forall integer k; 0 <= k < i ==>
      \forall integer p; k < p < rows ==> sum_row(matrix[k], cols) <= sum_row(matrix[p], cols);
      loop invariant \forall integer k; i <= k < j ==>
      (\forall integer p; k <= p < rows ==>
      \exists integer old_r; 0 <= old_r < \old(rows) &&
      \exists integer old_c; 0 <= old_c < \old(cols) &&
      matrix[k][p] == \at(matrix[k][p], LoopInv)); // Permutation within inner loop
      loop assigns j, matrix[0..rows-1][0..cols-1];
      loop variant rows - j;
    */
    for (int j = i + 1; j < rows; j++) {
      /*@
        requires i < rows;
        requires j < rows;
        requires cols > 0;
        requires \valid_read(matrix + i);
        requires \valid_read(matrix + j);
        requires \valid_read(*(matrix + i) + (0..cols-1));
        requires \valid_read(*(matrix + j) + (0..cols-1));
        requires sum_row(matrix[i], cols) <= 2000000000;
        requires sum_row(matrix[j], cols) <= 2000000000;
        assigns matrix[i][0..cols-1], matrix[j][0..cols-1];
        // Ensures that if swap occurs, the elements are correctly exchanged.
        // If not, matrix remains unchanged.
        ensures (sum_row(\at(matrix[i], Pre), cols) > sum_row(\at(matrix[j], Pre), cols)) ==>
        (\forall integer k; 0 <= k < cols ==> matrix[i][k] == \at(matrix[j][k], Pre) && matrix[j][k] == \at(matrix[i][k], Pre));
        ensures (sum_row(\at(matrix[i], Pre), cols) <= sum_row(\at(matrix[j], Pre), cols)) ==>
        (\forall integer k; 0 <= k < cols ==> matrix[i][k] == \at(matrix[i][k], Pre) && matrix[j][k] == \at(matrix[j][k], Pre));
      */
      if (sum_row(matrix[i], cols) > sum_row(matrix[j], cols)) {
        // Swap rows
        /*@
          loop invariant 0 <= k && k <= cols;
          loop invariant \forall integer p; 0 <= p < k ==>
          (\at(matrix[i][p], LoopEntry) == \at(matrix[j][p], LoopEntry) &&
          \at(matrix[j][p], LoopEntry) == matrix[i][p]);
          loop assigns k, matrix[i][0..cols-1], matrix[j][0..cols-1];
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
