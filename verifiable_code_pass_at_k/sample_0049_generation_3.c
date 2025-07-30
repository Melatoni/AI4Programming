// Task ID: 49
// Generation: 3

/*@
  // Rule II.1: Defining an axiomatic block for recursive logic.
  axiomatic GetColumn {
  logic integer get_column_element(int* arr, int rows, int cols, int r, int c)
  reads arr[0..rows*cols - 1];

  axiom get_column_element_base:
  \forall int* arr, int rows, int cols, int r, int c;
  0 <= r < rows && 0 <= c < cols ==> get_column_element(arr, rows, cols, r, c) == arr[r * cols + c];
  }
*/

/*@
  requires rows >= 0;
  requires cols >= 0;
  requires 0 <= col_index < cols;
  requires \valid_read(arr + (0 .. rows * cols - 1));
  requires \valid_write(result_arr + (0 .. rows - 1));
  assigns result_arr[0 .. rows - 1];

  // Rule II.3: Using logical equivalence for boolean-like return.
  ensures \forall integer i; 0 <= i < rows ==> result_arr[i] == get_column_element(arr, rows, cols, i, col_index);
  ensures \result == rows; // Indicates the number of elements copied.
*/
int extract_column(int* arr, int rows, int cols, int col_index, int* result_arr) {
  /*@
    loop invariant 0 <= i <= rows;
    loop invariant \forall integer k; 0 <= k < i ==> result_arr[k] == get_column_element(arr, rows, cols, k, col_index);
    loop assigns result_arr[0 .. rows - 1], i;
    loop variant rows - i;
  */
  for (int i = 0; i < rows; ++i) {
    result_arr[i] = arr[i * cols + col_index];
  }
  return rows;
}
