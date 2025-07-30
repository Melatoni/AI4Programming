// Task ID: 40
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule I.3: Array pointer decay.

  axiomatic Histogram {
    logic integer count_val(int val, int* arr, int size);
    logic integer count_val_2d(int val, int** arr, int rows, int cols);

    axiom count_val_base:
      \forall int val, int* arr, int size;
        size <= 0 ==> count_val(val, arr, size) == 0;

    axiom count_val_recursive:
      \forall int val, int* arr, int size;
        size > 0 ==> count_val(val, arr, size) == (arr[size - 1] == val ? 1 : 0) + count_val(val, arr, size - 1);

    axiom count_val_2d_base:
      \forall int val, int** arr, int rows, int cols;
        rows <= 0 ==> count_val_2d(val, arr, rows, cols) == 0;

    // Helper axiom: Sum of counts from a row
    lemma count_val_2d_row_sum:
      \forall int val, int** arr, int rows, int cols, integer r;
        0 <= r < rows ==>
        count_val_2d(val, arr, r + 1, cols) == count_val_2d(val, arr, r, cols) + count_val(val, arr[r], cols);
  }
*/

/*@
  // Rule I.3: `matrix` decays to `int (*)[cols]`.
  // Rule II.5: Prevent potential out-of-bounds access if `rows` or `cols` are negative.
  requires rows >= 0 && cols >= 0;
  // Rule II.5: Prevent `matrix` from being NULL if `rows` > 0.
  requires rows == 0 || matrix != \null;
  // Rule II.5: Prevent inner arrays from being NULL if `cols` > 0 and `rows` > 0.
  requires rows == 0 || cols == 0 || \forall integer i; 0 <= i < rows ==> matrix[i] != \null;

  // Rule II.5: Ensure `max_val` and `min_val` are within reasonable bounds for array indexing.
  // Assuming frequency array size is `max_val - min_val + 1`.
  requires max_val >= min_val;
  requires max_val - min_val + 1 >= 0; // Check for potential overflow if max_val - min_val is very large.

  // Rule II.5: Ensure `freq` array has sufficient size.
  requires freq != \null;
  requires freq_size >= (max_val - min_val + 1);

  assigns freq[0..(max_val - min_val)]; // Rule III.3: Correct range syntax.

  // Rule II.3: Ensures clause with logical equivalence for boolean-like functions.
  // This function doesn't return a boolean, but sets an output array.
  // The postcondition should state what `freq` contains.
  ensures \forall integer v; min_val <= v <= max_val ==> freq[v - min_val] == count_val_2d(v, matrix, rows, cols);
*/
void get_frequency(int* matrix[], int rows, int cols, int* freq, int freq_size, int min_val, int max_val) {
    /*@
      loop invariant 0 <= k <= (max_val - min_val);
      loop invariant \forall integer i; 0 <= i < k ==> freq[i] == 0;
      loop assigns k, freq[0..(max_val - min_val)];
      loop variant (max_val - min_val) - k;
    */
    for (int k = 0; k <= (max_val - min_val); k++) {
        freq[k] = 0;
    }

    /*@
      loop invariant 0 <= i <= rows;
      loop invariant \forall integer val; min_val <= val <= max_val ==>
        freq[val - min_val] == count_val_2d(val, matrix, i, cols);
      loop assigns i, freq[0..(max_val - min_val)];
      loop variant rows - i;
    */
    for (int i = 0; i < rows; i++) {
        /*@
          loop invariant 0 <= j <= cols;
          loop invariant \forall integer val; min_val <= val <= max_val ==>
            freq[val - min_val] == count_val_2d(val, matrix, i, cols) + count_val(val, matrix[i], j);
          loop assigns j, freq[0..(max_val - min_val)];
          loop variant cols - j;
        */
        for (int j = 0; j < cols; j++) {
            // Rule II.5: Check for potential out-of-bounds access for matrix[i][j] and freq[].
            // This is handled by requires clauses for matrix and freq, and the loop invariants.
            if (matrix[i][j] >= min_val && matrix[i][j] <= max_val) {
                freq[matrix[i][j] - min_val]++;
            }
        }
    }
}
