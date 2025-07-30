// Task ID: 40
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: int for booleans.
  // Rule I.3: Array pointer decay - arr is int (*arr)[cols].

  axiomatic IntRange {
    // Rule II.1: Recursive logic for complexity.
    // Defines a property that all elements in a 2D array are within a specific range.
    logic boolean all_elements_in_range(int rows, int cols, int arr[rows][cols], int min_val, int max_val) =
      rows == 0 ||
      (cols == 0 && all_elements_in_range(rows - 1, \at(cols, Pre), arr, min_val, max_val)) ||
      (rows > 0 && cols > 0 &&
       min_val <= arr[rows - 1][cols - 1] <= max_val &&
       all_elements_in_range(rows, cols - 1, arr, min_val, max_val) &&
       all_elements_in_range(rows - 1, \at(cols, Pre), arr, min_val, max_val));

    // Helper axiom for all_elements_in_range when cols is 0.
    // This axiom helps the prover understand the base case for `cols` more directly.
    axiom all_elements_in_range_cols_zero:
      \forall int r, c, int arr_val[r][c], int min, max;
        c == 0 ==> all_elements_in_range(r, c, arr_val, min, max) == \true;

    // Helper axiom: If all elements are in range, then for any valid index, the element is in range.
    axiom all_elements_in_range_implies_element_in_range:
      \forall int r, c, int arr_val[r][c], int min, max, int i, j;
        0 <= i < r && 0 <= j < c &&
        all_elements_in_range(r, c, arr_val, min, max) ==>
        min <= arr_val[i][j] <= max;
  }
*/

/*@
  requires rows >= 0;
  requires cols >= 0;
  // Rule II.5: Prevent potential issues with array indexing if min_val > max_val.
  requires min_val <= max_val;
  // The size of the frequencies array must be sufficient.
  requires \valid(frequencies + (max_val - min_val));
  // All elements in the input array must be within the specified range.
  requires all_elements_in_range(rows, cols, arr, min_val, max_val);

  assigns frequencies[0 .. (max_val - min_val)];

  // The ensures clause guarantees that each frequency count is correct.
  ensures \forall integer k;
    min_val <= k <= max_val ==>
    frequencies[k - min_val] == (\num_of(integer r, integer c; 0 <= r < rows && 0 <= c < cols && arr[r][c] == k));
*/
void get_element_frequencies(int rows, int cols, int arr[rows][cols], int min_val, int max_val, int frequencies[]) {
    int range_size = max_val - min_val + 1;

    /*@
      loop invariant 0 <= i <= range_size;
      loop invariant \forall integer k; 0 <= k < i ==> frequencies[k] == 0;
      loop assigns frequencies[0 .. range_size - 1];
      loop variant range_size - i;
    */
    for (int i = 0; i < range_size; ++i) {
        frequencies[i] = 0;
    }

    /*@
      loop invariant 0 <= r <= rows;
      loop invariant \forall integer row_idx; 0 <= row_idx < r ==>
        \forall integer col_idx; 0 <= col_idx < cols ==>
          frequencies[arr[row_idx][col_idx] - min_val] ==
            (\num_of(integer i, integer j;
                     0 <= i <= row_idx && 0 <= j < cols && arr[i][j] == arr[row_idx][col_idx]) +
             (\num_of(integer i, integer j;
                      0 <= i < row_idx && 0 <= j < cols && arr[i][j] == arr[row_idx][col_idx])));

      loop invariant \forall integer val_k; min_val <= val_k <= max_val ==>
        frequencies[val_k - min_val] == (\num_of(integer i, integer j;
                                                0 <= i < r && 0 <= j < cols && arr[i][j] == val_k));

      loop assigns frequencies[0 .. range_size - 1], r, c; // c is assigned in inner loop
      loop variant rows - r;
    */
    for (int r = 0; r < rows; ++r) {
        /*@
          loop invariant 0 <= c <= cols;
          loop invariant \forall integer val_k; min_val <= val_k <= max_val ==>
            frequencies[val_k - min_val] == (\num_of(integer i, integer j;
                                                    0 <= i < r && 0 <= j < cols && arr[i][j] == val_k) +
                                            (\num_of(integer j_prime;
                                                     0 <= j_prime < c && arr[r][j_prime] == val_k)));

          loop assigns frequencies[0 .. range_size - 1], c;
          loop variant cols - c;
        */
        for (int c = 0; c < cols; ++c) {
            // Rule II.5: arr[r][c] is guaranteed to be in range by the pre-condition,
            // so arr[r][c] - min_val will be a valid index.
            frequencies[arr[r][c] - min_val]++;
        }
    }
}
