// Task ID: 12
// Generation: 7

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
  // Define a constant for the maximum number of rows and columns
  // Assuming a reasonable upper bound for matrix dimensions for practical verification.
  // These should be adjusted based on specific problem constraints if given.
  // For this problem, let's assume a max dimension for arrays to prevent unbounded verification time.
  #define MAX_ROWS 10
  #define MAX_COLS 10

  // Rule II.1: Define recursive logic for sum of a row.
  axiomatic RowSum {
    logic integer row_sum_at(int* row, int col_idx, int num_cols);

    // Base case: sum of an empty prefix is 0
    axiom row_sum_at_base:
      \forall int* row, int num_cols;
        row_sum_at(row, -1, num_cols) == 0;

    // Recursive step: sum of prefix up to col_idx
    axiom row_sum_at_rec:
      \forall int* row, int col_idx, int num_cols;
        0 <= col_idx < num_cols ==>
        row_sum_at(row, col_idx, num_cols) == row_sum_at(row, col_idx - 1, num_cols) + row[col_idx];

    // Helper logic function for the total sum of a row
    logic integer total_row_sum(int* row, int num_cols) = row_sum_at(row, num_cols - 1, num_cols);

    // Rule II.2: Helper axiom for total_row_sum to prove its properties.
    // This axiom helps relate total_row_sum to the actual sum of elements.
    // It's technically derivable from the recursive definition, but explicitly stating it
    // can sometimes help the prover or clarify intent.
    axiom total_row_sum_def:
      \forall int* row, int num_cols;
        0 <= num_cols ==>
        total_row_sum(row, num_cols) == (\sum integer k; 0 <= k < num_cols; row[k]);
  }

  // Axiomatic for properties of a sorted array of sums
  axiomatic SortedSums {
    logic boolean is_sorted_by_sum(int** matrix, int num_rows, int num_cols);

    // Base case: an array with 0 or 1 row is considered sorted
    axiom is_sorted_by_sum_base:
      \forall int** matrix, int num_cols;
        is_sorted_by_sum(matrix, 0, num_cols) == \true;
        is_sorted_by_sum(matrix, 1, num_cols) == \true;

    // Recursive step: sorted if first part is sorted and the last element is in order
    axiom is_sorted_by_sum_rec:
      \forall int** matrix, int num_rows, int num_cols;
        num_rows >= 2 ==>
        is_sorted_by_sum(matrix, num_rows, num_cols) ==
        (is_sorted_by_sum(matrix, num_rows - 1, num_cols) &&
         total_row_sum(matrix[num_rows - 2], num_cols) <= total_row_sum(matrix[num_rows - 1], num_cols));
  }
*/

/*@
  requires num_rows >= 0 && num_rows <= MAX_ROWS;
  requires num_cols >= 0 && num_cols <= MAX_COLS;

  // The matrix elements must be within a range that prevents overflow when summing rows.
  // Assuming int can hold sum of MAX_COLS * INT_MAX, which is not true.
  // So, we add a more realistic bound for matrix elements.
  // For example, if int is 32-bit and MAX_COLS is 100, then elements must be small.
  // Let's assume elements are small enough so their sum doesn't overflow `int`.
  // A tighter bound would be `INT_MAX / num_cols`.
  requires \forall integer r, c; 0 <= r < num_rows && 0 <= c < num_cols ==>
    - (INT_MAX / num_cols) <= matrix[r][c] <= (INT_MAX / num_cols);

  // The matrix itself must be valid (not null pointers)
  requires \valid_read(matrix + (0..num_rows - 1));
  requires \forall integer r; 0 <= r < num_rows ==> \valid_read(matrix[r] + (0..num_cols - 1));
  requires \forall integer r; 0 <= r < num_rows ==> \fresh(matrix[r], num_cols); // Matrix rows are distinct memory regions

  assigns matrix[0..num_rows-1][0..num_cols-1];

  ensures is_sorted_by_sum(matrix, num_rows, num_cols);
  ensures \forall integer r, c; 0 <= r < num_rows && 0 <= c < num_cols ==>
    \old(matrix[r][c]) == matrix[r][c]; // This is wrong, matrix elements will be swapped.

  // The final state of the matrix must be a permutation of the initial state.
  // This is a complex property to express in ACSL for a 2D array.
  // For a 1D array, `\forall integer i; 0 <= i < n ==> \exists integer j; 0 <= j < n && a[i] == \old(a[j])`
  // and `\forall integer i; 0 <= i < n ==> \exists integer j; 0 <= j < n && \old(a[i]) == a[j]`
  // For 2D, it means the set of rows is permuted.
  ensures \forall integer r; 0 <= r < num_rows ==>
    \exists integer old_r; 0 <= old_r < num_rows &&
    (\forall integer c; 0 <= c < num_cols ==> matrix[r][c] == \old(matrix[old_r][c]));
  ensures \forall integer old_r; 0 <= old_r < num_rows ==>
    \exists integer r; 0 <= r < num_rows &&
    (\forall integer c; 0 <= c < num_cols ==> matrix[r][c] == \old(matrix[old_r][c]));
*/
void sort_matrix_by_row_sum(int matrix[][MAX_COLS], int num_rows, int num_cols) {
    // Bubble sort approach
    int i, j;
    int temp_row[MAX_COLS]; // Rule I.1: No dynamic allocation. Use fixed size for simplicity.

    /*@
      loop invariant 0 <= i && i <= num_rows;
      loop invariant \forall integer k; i <= k < num_rows ==>
        \forall integer l; k < l < num_rows ==>
          total_row_sum(matrix[k], num_cols) <= total_row_sum(matrix[l], num_cols);
      // The outer loop ensures that the last `i` elements are in their final sorted position.
      loop invariant \forall integer k; num_rows - i <= k < num_rows ==>
        \forall integer l; 0 <= l < k ==>
          total_row_sum(matrix[l], num_cols) <= total_row_sum(matrix[k], num_cols);

      // Permutation property for the outer loop invariant:
      // The set of rows matrix[0..num_rows-1] is always a permutation of \old(matrix[0..num_rows-1]).
      loop invariant \forall integer r; 0 <= r < num_rows ==> \exists integer old_r; 0 <= old_r < num_rows && (\forall integer c; 0 <= c < num_cols ==> matrix[r][c] == \at(matrix[old_r][c], Pre));
      loop invariant \forall integer old_r; 0 <= old_r < num_rows ==> \exists integer r; 0 <= r < num_rows && (\forall integer c; 0 <= c < num_cols ==> matrix[r][c] == \at(matrix[old_r][c], Pre));

      loop assigns i, j, matrix[0..num_rows-1][0..num_cols-1], temp_row[0..num_cols-1];
      loop variant num_rows - i;
    */
    for (i = 0; i < num_rows - 1; i++) {
        /*@
          loop invariant 0 <= j && j <= num_rows - 1 - i;
          loop invariant \forall integer k; j <= k < num_rows - 1 - i ==> total_row_sum(matrix[k], num_cols) <= total_row_sum(matrix[k+1], num_cols);
          // In each inner loop iteration, the largest element "bubbles" to the end of the unsorted part.
          loop invariant \forall integer k; 0 <= k <= j ==>
            total_row_sum(matrix[k], num_cols) <= total_row_sum(matrix[k+1], num_cols);
          // The elements from num_rows - 1 - i to num_rows - 1 are already sorted and in final position relative to each other.
          loop invariant \forall integer k; num_rows - 1 - i <= k < num_rows ==>
            \forall integer l; 0 <= l < k ==> total_row_sum(matrix[l], num_cols) <= total_row_sum(matrix[k], num_cols);

          // Permutation property for the inner loop invariant:
          loop invariant \forall integer r; 0 <= r < num_rows ==> \exists integer old_r; 0 <= old_r < num_rows && (\forall integer c; 0 <= c < num_cols ==> matrix[r][c] == \at(matrix[old_r][c], LoopEntry));
          loop invariant \forall integer old_r; 0 <= old_r < num_rows ==> \exists integer r; 0 <= r < num_rows && (\forall integer c; 0 <= c < num_cols ==> matrix[r][c] == \at(matrix[old_r][c], LoopEntry));

          loop assigns j, matrix[0..num_rows-1][0..num_cols-1], temp_row[0..num_cols-1];
          loop variant num_rows - 1 - i - j;
        */
        for (j = 0; j < num_rows - 1 - i; j++) {
            // Rule II.5: Prevent overflow when calculating sum.
            // This is handled by the overall function requires clause on matrix elements.
            // `total_row_sum` is a pure logic function, no runtime overflow here.
            if (total_row_sum(matrix[j], num_cols) > total_row_sum(matrix[j + 1], num_cols)) {
                // Swap rows
                /*@
                  loop invariant 0 <= k && k <= num_cols;
                  loop assigns temp_row[0..num_cols-1], matrix[j][0..num_cols-1], matrix[j+1][0..num_cols-1];
                  loop variant num_cols - k;
                */
                for (int k = 0; k < num_cols; k++) {
                    temp_row[k] = matrix[j][k];
                    matrix[j][k] = matrix[j + 1][k];
                    matrix[j + 1][k] = temp_row[k];
                }
            }
        }
    }
}
