// Task ID: 49
// Generation: 1

/*@
  // Rule II.1: Using axiomatic for complex logic (summation is not directly needed here, but good practice for properties)
  axiomatic GetColumnElement {
    logic integer get_element_at_col(int** arr, integer row, integer col, integer rows, integer cols)
      reads arr[0..rows-1][0..cols-1];

    axiom get_element_at_col_def:
      \forall int** arr, integer row, integer col, integer rows, integer cols;
        0 <= row < rows && 0 <= col < cols ==>
        get_element_at_col(arr, row, col, rows, cols) == arr[row][col];
  }
*/

/*@
  requires rows > 0;
  requires cols > 0;
  requires 0 <= col_index < cols;

  // Rule I.1: No standard libraries, so no NULL check for arr directly.
  // We assume valid memory for arr based on the contract.
  // Rule I.3: arr decays to int (*arr)[cols], so ACSL needs to match.
  requires \valid_read(arr) && \valid_read(arr[0..rows-1]);
  requires \forall integer i; 0 <= i < rows ==> \valid_read(arr[i][0..cols-1]);

  // The result array must be allocated by the caller with enough space.
  requires \valid(result);
  requires \separated(arr, result);

  assigns result[0..rows-1];

  // Rule II.3: Ensures clause for boolean-like functions uses <==> pattern.
  // Here, it's not boolean-like, but for functions modifying arrays, we ensure the content.
  ensures \forall integer i; 0 <= i < rows ==> result[i] == arr[i][col_index];
  ensures \result == result; // Return the pointer to the modified result array.
*/
int* extract_column(int** arr, int rows, int cols, int col_index, int* result) {
  /*@
    loop invariant 0 <= i <= rows;
    loop invariant \forall integer k; 0 <= k < i ==> result[k] == arr[k][col_index];
    loop assigns i, result[0..rows-1];
    loop variant rows - i;
  */
  for (int i = 0; i < rows; ++i) {
    result[i] = arr[i][col_index];
  }
  return result;
}
