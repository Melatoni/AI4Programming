// Task ID: 49
// Generation: 0

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This axiomatic block defines a property that checks if a sub-array contains only zeros.
  axiomatic AllZeros {
    logic boolean all_zeros(int* arr, integer len);

    axiom all_zeros_base:
      \forall int* arr; all_zeros(arr, 0) == \true;

    axiom all_zeros_recursive:
      \forall int* arr, integer len;
        len > 0 ==> (all_zeros(arr, len) <==> (arr[len-1] == 0 && all_zeros(arr, len-1)));
  }
*/

/*@
  requires rows >= 0;
  requires cols >= 0;
  requires 0 <= col_idx < cols; // Rule II.5: Prevent out-of-bounds access
  // Rule II.5: Ensure result array has enough space.
  requires \valid(result_arr + (0..rows-1));

  // Rule I.3: Array parameter `matrix[rows][cols]` decays to `int (*matrix)[cols]`.
  // The axiomatic function `all_zeros` expects `int*`, so we need to be careful if we
  // were to apply it to a row directly. For this problem, we are just extracting,
  // so `matrix` itself is just a pointer to the first row (which is an array).
  requires \valid_read(matrix + (0..rows-1));
  requires \for_all integer i; 0 <= i < rows ==> \valid_read(matrix[i] + (0..cols-1));

  assigns result_arr[0..rows-1];

  // Rule II.3: Use logical equivalence for boolean-like functions (even though this returns void).
  // This ensures clause states that each element in result_arr is the col_idx-th element
  // of the corresponding row in matrix.
  ensures \for_all integer i; 0 <= i < rows ==> result_arr[i] == matrix[i][col_idx];
*/
void extract_column(int rows, int cols, int matrix[rows][cols], int col_idx, int result_arr[rows]) {
  /*@
    loop invariant 0 <= i <= rows;
    // Rule II.4: Invariant for the loop.
    // All elements processed so far match the expected value.
    loop invariant \for_all integer k; 0 <= k < i ==> result_arr[k] == matrix[k][col_idx];
    loop assigns i, result_arr[0..rows-1];
    // Rule II.4: Loop variant for termination.
    loop variant rows - i;
  */
  for (int i = 0; i < rows; i++) {
    result_arr[i] = matrix[i][col_idx];
  }
}
