// Task ID: 49
// Generation: 2

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This axiomatic block defines a property that checks if a sub-array contains only zeros.
  axiomatic AllZeros {
    logic boolean all_zeros_in_row(int* arr, int start, int end) reads arr[start..end];

    axiom all_zeros_in_row_base:
      \forall int* arr, int start;
        all_zeros_in_row(arr, start, start-1) == \true;

    axiom all_zeros_in_row_recursive:
      \forall int* arr, int start, int end;
        start <= end ==>
        all_zeros_in_row(arr, start, end) == (arr[end] == 0 && all_zeros_in_row(arr, start, end-1));
  }
*/

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This axiomatic block defines a property that checks if an element at a given index
  // in a 2D array is equal to a specified value.
  axiomatic ElementAtEquals {
    logic integer get_element_at(int (*arr)[], int row_idx, int col_idx);

    axiom get_element_at_def:
      \forall int (*arr)[], int row_idx, int col_idx;
        get_element_at(arr, row_idx, col_idx) == arr[row_idx][col_idx];
  }
*/


/*@
  requires rows > 0;
  requires cols > 0;
  requires 0 <= col_index < cols;
  
  // Rule II.5: Prevent potential overflow if rows * col_index is used for indexing.
  // Although not directly used for indexing in this function, it's good practice
  // to constrain array sizes if they might lead to large memory allocations or
  // other operations involving their product.
  // For `int` types, `INT_MAX` is usually 2147483647.
  // A conservative bound for `rows * cols` would be `INT_MAX / sizeof(int)`.
  // Since we are not allocating memory, this specific `requires` is less critical,
  // but it's a good reminder for general array processing.
  // For simplicity, let's assume `rows * cols` won't overflow int.
  
  // Rule I.3: `arr` decays to `int (*)[]`.
  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The result_array will contain the elements `arr[i][col_index]` for `0 <= i < rows`.
  ensures \forall integer i; 0 <= i < rows ==> result_array[i] == get_element_at(arr, i, col_index);
  ensures \result == rows; // Indicates how many elements were extracted.
  assigns result_array[0..rows-1];
*/
int extract_column_elements(int arr[][100], int rows, int cols, int col_index, int result_array[]) {
    /*@
      loop invariant 0 <= i <= rows;
      // Rule II.4: Invariant stating that elements up to i-1 have been correctly copied.
      loop invariant \forall integer k; 0 <= k < i ==> result_array[k] == get_element_at(arr, k, col_index);
      loop assigns i, result_array[0..rows-1]; // Specify the range of elements assigned.
      loop variant rows - i;
    */
    for (int i = 0; i < rows; i++) {
        result_array[i] = arr[i][col_index];
    }
    return rows;
}
