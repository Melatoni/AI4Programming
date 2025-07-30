// Task ID: 23
// Generation: 2

/*@
  // Axiomatic block for recursive logic and helper axioms.
  // Rule II.1: Recursive logic for sum.
  // Rule I.3: Array pointer decay must be handled correctly.
*/
/*@
  axiomatic SumArray {
    logic integer sum_array(int* arr, integer len);

    axiom sum_array_empty:
      \forall int* arr;
        sum_array(arr, 0) == 0;

    axiom sum_array_recursive:
      \forall int* arr, integer len;
        len > 0 ==> sum_array(arr, len) == arr[len - 1] + sum_array(arr, len - 1);

    // Rule II.2: Helper axiom for sum range.
    // This helps prove that sum_array will not overflow if individual elements are constrained.
    // For simplicity, we assume elements are within int range and sum doesn't exceed INT_MAX.
    // More complex bounds would require more specific axioms or requires clauses.
    axiom sum_array_bounds:
      \forall int* arr, integer len;
        (\forall integer i; 0 <= i < len ==> -2000000000 <= arr[i] <= 2000000000) ==>
        -2000000000LL * len <= sum_array(arr, len) <= 2000000000LL * len;
  }
*/

/*@
  // Define an axiomatic block for `max_sum_in_list_of_lists` to use it in other contracts if needed.
  // Although not strictly necessary for this problem, it demonstrates the pattern.
  axiomatic MaxSumLogic {
    logic integer max_sum_of_sublists(int** matrix, integer rows, integer* cols_len);

    // No specific axioms are needed here as the logic is directly implemented by sum_array
    // and a simple max comparison.
  }
*/


/*@
  requires rows >= 0;
  requires \valid_read(cols_len + (0..rows-1));
  requires \valid_read(matrix + (0..rows-1));

  // Pre-conditions to prevent integer overflow when calculating sum_array for each row,
  // assuming each element is within standard int range and `rows` is not excessively large.
  // The specific value 100000 is chosen to allow sum_array to be within int range for up to 100000 elements,
  // assuming an average value of 20000 for each element. This needs to be adjusted based on expected data.
  // A safer approach for general use would involve using long long for sums or more rigorous overflow checks.
  requires \forall integer i; 0 <= i < rows ==> cols_len[i] >= 0 && cols_len[i] <= 100000;
  requires \forall integer i; 0 <= i < rows ==> \valid_read(matrix[i] + (0..cols_len[i]-1));
  
  // Ensures that if there are no rows, the maximum sum is 0.
  // If there are rows, the result is the maximum of the sums of each sublist.
  ensures rows == 0 ==> \result == 0;
  ensures rows > 0 ==>
    \result == (\max integer i; 0 <= i < rows; sum_array(matrix[i], cols_len[i]));

  // No assigns clause needed if we only read inputs and return a value.
  assigns \nothing;
*/
int find_max_sum_of_sublists(int** matrix, int rows, int* cols_len) {
    if (rows == 0) {
        return 0;
    }

    // Initialize max_sum with the sum of the first sublist.
    // Rule II.5: Requires clause ensures cols_len[0] is valid.
    /*@
      // Requires for sum_array to verify the first sum.
      requires 0 <= cols_len[0] <= 100000;
      requires \valid_read(matrix[0] + (0..cols_len[0]-1));
      // Ensures the initial value matches sum_array(matrix[0], cols_len[0]).
      ensures \result == sum_array(matrix[0], cols_len[0]);
    */
    int max_sum = sum_array(matrix[0], cols_len[0]);

    /*@
      loop invariant 1 <= i <= rows;
      // The max_sum found so far is indeed the maximum among the sublists processed up to i-1.
      loop invariant max_sum == (\max integer k; 0 <= k < i; sum_array(matrix[k], cols_len[k]));
      loop assigns i, max_sum;
      loop variant rows - i;
    */
    for (int i = 1; i < rows; i++) {
        /*@
          // Requires for sum_array to verify the current sum.
          requires 0 <= cols_len[i] <= 100000;
          requires \valid_read(matrix[i] + (0..cols_len[i]-1));
          ensures \result == sum_array(matrix[i], cols_len[i]);
        */
        int current_sum = sum_array(matrix[i], cols_len[i]);

        // Rule II.5: Prevent potential overflow if current_sum or max_sum are near INT_MAX/INT_MIN
        // and their comparison could lead to issues.
        // For simple max, this is less critical, but good practice.
        if (current_sum > max_sum) {
            max_sum = current_sum;
        }
    }

    return max_sum;
}
