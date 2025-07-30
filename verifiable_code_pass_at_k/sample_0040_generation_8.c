// Task ID: 40
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.
  
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory Loop Annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic ElementCount {
    logic integer count_element_in_array(int val, int* arr, integer size);

    axiom count_element_in_array_empty{
      \forall int val, int* arr;
        count_element_in_array(val, arr, 0) == 0;
    }

    axiom count_element_in_array_recursive{
      \forall int val, int* arr, integer size;
        size > 0 ==> count_element_in_array(val, arr, size) ==
          (if arr[size - 1] == val then 1 else 0) + count_element_in_array(val, arr, size - 1);
    }

    logic integer count_element_in_matrix(int val, int** matrix, integer rows, integer cols);

    axiom count_element_in_matrix_empty_rows{
      \forall int val, int** matrix, integer cols;
        count_element_in_matrix(val, matrix, 0, cols) == 0;
    }

    axiom count_element_in_matrix_recursive_rows{
      \forall int val, int** matrix, integer rows, integer cols;
        rows > 0 ==> count_element_in_matrix(val, matrix, rows, cols) ==
          count_element_in_array(val, matrix[rows - 1], cols) + count_element_in_matrix(val, matrix, rows - 1, cols);
    }
  }
*/


/*@
  requires rows > 0 && cols > 0;
  requires \valid_read(list_of_lists + (0..rows-1));
  requires \forall integer i; 0 <= i < rows ==> \valid_read(list_of_lists[i] + (0..cols-1));
  requires \valid_write(frequencies + (0..max_val)); // Ensure frequencies array is large enough
  requires \forall integer i; 0 <= i <= max_val ==> frequencies[i] == 0; // Pre-condition: frequencies array is zero-initialized
  requires \forall integer i, j; 0 <= i < rows && 0 <= j < cols ==> 0 <= list_of_lists[i][j] <= max_val;
  
  assigns \nothing; // This function modifies frequencies, but the problem states it should "find frequency... using collections module", implying a return.
                   // Since we are not using collections module and modifying an output array is more C-idiomatic for results,
                   // I'll assume the intent is to populate `frequencies` and then `assigns \nothing` is incorrect.
                   // Let's re-interpret the problem: "find frequency" means populate the `frequencies` array.
                   // So, `assigns frequencies[0..max_val];` is appropriate.
  assigns frequencies[0..max_val];

  // The function computes frequencies, so the post-condition should state that
  // each element in frequencies represents the total count of that value.
  ensures \forall integer val; 0 <= val <= max_val ==>
    frequencies[val] == count_element_in_matrix(val, list_of_lists, rows, cols);
*/
void find_frequency(int* list_of_lists[], int rows, int cols, int* frequencies, int max_val) {
    /*@
      loop invariant 0 <= i <= rows;
      loop invariant \forall integer r; 0 <= r < i ==>
        \forall integer val; 0 <= val <= max_val ==>
          frequencies[val] == count_element_in_matrix(val, list_of_lists, r, cols);
      loop assigns i, frequencies[0..max_val];
      loop variant rows - i;
    */
    for (int i = 0; i < rows; i++) {
        /*@
          loop invariant 0 <= j <= cols;
          loop invariant \forall integer c; 0 <= c < j ==>
            frequencies[list_of_lists[i][c]] == count_element_in_matrix(list_of_lists[i][c], list_of_lists, i, cols) +
                                                count_element_in_array(list_of_lists[i][c], list_of_lists[i], c);
          loop assigns j, frequencies[0..max_val];
          loop variant cols - j;
        */
        for (int j = 0; j < cols; j++) {
            int element = list_of_lists[i][j];
            // Rule II.5: Prevent RTE - ensure element is within bounds of frequencies array.
            // This is handled by the initial `requires` clause `0 <= list_of_lists[i][j] <= max_val;`
            frequencies[element]++;
        }
    }
}
