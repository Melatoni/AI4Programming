// Task ID: 49
// Generation: 5

/*@
  // Rule II.1: Using axiomatic block for recursive logic.
  // Rule I.3: Correct pointer type for 2D array.
  axiomatic GetElement {
  logic integer get_element(int *arr, integer row, integer col_idx, integer num_cols)
  reads arr[row * num_cols + col_idx];

  axiom get_element_def:
  \forall int *arr, integer row, integer col_idx, integer num_cols;
  get_element(arr, row, col_idx, num_cols) == arr[row * num_cols + col_idx];
  }
*/


/*@
  requires num_rows >= 0;
  requires num_cols > 0; // Each row must have at least one column for col_idx to be valid
  requires 0 <= col_idx < num_cols; // col_idx must be a valid column index
  requires \valid_read(matrix + (0..(num_rows * num_cols) - 1));
  requires \valid(result + (0..num_rows - 1));

  assigns result[0..num_rows-1];

  // Rule II.3: Ensures clause for boolean-like function (though this is not boolean,
  // it shows how direct value assignments are stated).
  ensures \forall integer r; 0 <= r < num_rows ==> result[r] == get_element(matrix, r, col_idx, num_cols);
*/
void extract_column(int *matrix, int num_rows, int num_cols, int col_idx, int *result) {
  /*@
    loop invariant 0 <= r <= num_rows;
    loop invariant \forall integer i; 0 <= i < r ==> result[i] == get_element(matrix, i, col_idx, num_cols);
    loop assigns r, result[0..num_rows-1];
    loop variant num_rows - r;
  */
  for (int r = 0; r < num_rows; ++r) {
    result[r] = matrix[r * num_cols + col_idx];
  }
}
