// Task ID: 40
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1, II.2: Recursive logic for complexity, helper axioms.
  // We need an axiomatic block to define properties of list of lists.
  // For this problem, we'll model the input as a 2D array, where each row
  // represents an inner list and the first element of each inner list
  // indicates its actual length to handle variable-length inner lists.
  // This is a common pattern for Frama-C when dealing with dynamic-like structures.

  // Let's define a maximum possible value for elements to prevent overflow
  // if we were to count them in an auxiliary array.
  // For this problem, we'll assume elements are non-negative and within int range.
  // The problem asks for frequency, so we'll need a way to store counts.
  // A simple approach is to count occurrences of a specific value.
  // If we were to count all frequencies, we'd need an output array.

  // Let's refine the problem: write a function that counts the occurrences
  // of a specific `target` integer within a given list of lists (represented as a 2D array).

  // Define properties of the 2D array structure
  axiomatic ListOfLists {
    // Represents the actual length of the inner list at row 'i'
    logic integer inner_list_len(int** arr, int rows, int i);

    // Axiom: The length must be non-negative and not exceed the allocated column size.
    // For simplicity, let's assume `arr[i][0]` stores the length of `arr[i][1..]`.
    // This is a common Frama-C pattern for "flexible" arrays.
    // Here, `inner_list_len(arr, rows, i)` will simply be `arr[i][0]`.
    // We need to ensure `arr[i][0]` is a valid length.

    // Let's simplify the input structure: a 2D array `int matrix[ROWS][COLS]`
    // where `matrix[i][0]` is the length of the valid elements in `matrix[i][1...matrix[i][0]]`.
    // This is a common Frama-C pattern for arrays with varying row lengths.

    // Axiom for `inner_list_len`:
    // It's simpler to directly use `matrix[i][0]` as the length within the
    // function's ACSL annotations, rather than defining a logic function for it,
    // unless we need to reason about its properties abstractly.
    // For this specific problem (counting frequency of a target),
    // we don't strictly need a recursive logic function for the *structure* itself,
    // but we will need one for the *count*.

    // Recursive logic function to count occurrences of `target` in an inner list from `start_idx`
    logic integer count_in_inner_list(int* inner_list, int len, int target, int start_idx);

    // Base case: If start_idx is beyond the length, count is 0.
    axiom count_in_inner_list_base:
      \forall int* inner_list, int len, int target, int start_idx;
        start_idx >= len ==> count_in_inner_list(inner_list, len, target, start_idx) == 0;

    // Recursive case:
    axiom count_in_inner_list_rec:
      \forall int* inner_list, int len, int target, int start_idx;
        start_idx < len ==>
          count_in_inner_list(inner_list, len, target, start_idx) ==
            (if inner_list[start_idx] == target then 1 else 0) +
            count_in_inner_list(inner_list, len, target, start_idx + 1);

    // Recursive logic function to count occurrences of `target` in the entire list of lists
    logic integer count_total_frequency(int** matrix, int rows, int cols, int target, int row_idx);

    // Base case: If row_idx is beyond the number of rows, total count is 0.
    axiom count_total_frequency_base:
      \forall int** matrix, int rows, int cols, int target, int row_idx;
        row_idx >= rows ==> count_total_frequency(matrix, rows, cols, target, row_idx) == 0;

    // Recursive case:
    axiom count_total_frequency_rec:
      \forall int** matrix, int rows, int cols, int target, int row_idx;
        row_idx < rows && matrix[row_idx][0] >= 0 && matrix[row_idx][0] < cols ==>
          count_total_frequency(matrix, rows, cols, target, row_idx) ==
            count_in_inner_list(matrix[row_idx], matrix[row_idx][0] + 1, target, 1) + // +1 for 0-index length, start from index 1 for elements
            count_total_frequency(matrix, rows, cols, target, row_idx + 1);

    // Helper axiom: If all elements are positive, count is non-negative.
    // Not strictly needed for this problem, but good for demonstrating Rule II.2.
    axiom count_non_negative:
      \forall int** matrix, int rows, int cols, int target, int row_idx;
        count_total_frequency(matrix, rows, cols, target, row_idx) >= 0;
  }
*/

/*@
  requires rows >= 0;
  requires cols >= 1; // Minimum 1 column for length at index 0.
  // Rule II.5: Prevent RTEs. Ensure matrix is valid.
  requires \valid_read(matrix + (0..rows-1));
  requires \forall integer i; 0 <= i < rows ==> \valid_read(matrix[i] + (0..cols-1));
  // Ensure the stored length in matrix[i][0] is valid.
  requires \forall integer i; 0 <= i < rows ==> matrix[i][0] >= 0 && matrix[i][0] < cols;

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions (though this returns int count).
  // For count functions, the result directly corresponds to the logic function.
  ensures \result == count_total_frequency(matrix, rows, cols, target, 0);
*/
int find_frequency_of_target(int** matrix, int rows, int cols, int target) {
    int total_frequency = 0;

    /*@
      loop invariant 0 <= i <= rows;
      loop invariant total_frequency == count_total_frequency(matrix, i, cols, target, 0);
      loop assigns i, total_frequency;
      loop variant rows - i;
    */
    for (int i = 0; i < rows; i++) {
        // matrix[i][0] stores the actual length of the inner list (excluding the length itself).
        // The elements are matrix[i][1] to matrix[i][matrix[i][0]].
        int inner_list_len = matrix[i][0];

        /*@
          loop invariant 0 <= j <= inner_list_len + 1;
          loop invariant total_frequency ==
                           (\at(total_frequency, LoopEntry) +
                            count_in_inner_list(matrix[i], inner_list_len + 1, target, 1) -
                            count_in_inner_list(matrix[i], inner_list_len + 1, target, j));
          loop assigns j, total_frequency;
          loop variant inner_list_len + 1 - j;
        */
        for (int j = 1; j <= inner_list_len; j++) { // Start from index 1
            if (matrix[i][j] == target) {
                total_frequency++;
            }
        }
    }

    return total_frequency;
}
