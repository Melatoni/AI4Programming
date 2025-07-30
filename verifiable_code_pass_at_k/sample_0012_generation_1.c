// Task ID: 12
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic SumOfRow {
  logic integer sum_row_recursive(int R, int C, int* matrix, integer row_idx, integer col_idx) reads matrix[0..R*C-1];

  axiom sum_row_base:
    \forall int R, C, *matrix, row_idx;
    sum_row_recursive(R, C, matrix, row_idx, -1) == 0;

  axiom sum_row_recursive_step:
    \forall int R, C, *matrix, row_idx, col_idx;
    0 <= col_idx < C ==>
    sum_row_recursive(R, C, matrix, row_idx, col_idx) == matrix[row_idx * C + col_idx] + sum_row_recursive(R, C, matrix, row_idx, col_idx - 1);

  // Helper function to get the full sum of a row
  logic integer sum_row(int R, int C, int* matrix, integer row_idx) reads matrix[0..R*C-1];

  axiom sum_row_def:
    \forall int R, C, *matrix, row_idx;
    0 <= row_idx < R && C >= 0 ==>
    sum_row(R, C, matrix, row_idx) == sum_row_recursive(R, C, matrix, row_idx, C - 1);
}
*/

/*@
  // Helper predicate to check if the matrix rows are sorted by their sums
  predicate is_sorted_by_row_sum(int R, int C, int* matrix) =
    \forall integer i; 0 <= i < R - 1 ==> sum_row(R, C, matrix, i) <= sum_row(R, C, matrix, i + 1);

  // Helper predicate to check if the matrix elements are a permutation of the original
  predicate is_permutation(int R, int C, int* original_matrix, int* current_matrix) =
    \forall integer val;
      (\numof(integer i, j; 0 <= i < R && 0 <= j < C && original_matrix[i*C + j] == val)) ==
      (\numof(integer k, l; 0 <= k < R && 0 <= l < C && current_matrix[k*C + l] == val));
*/

/*@
  requires R > 0 && C > 0;
  requires \valid_read(matrix + (0..(R*C-1)));
  requires \valid(matrix + (0..(R*C-1))); // For modifications

  // Ensure no overflow when calculating row sums (assuming int is 32-bit)
  // Max int value is approx 2 * 10^9. If C is 1000, max element value is 2 * 10^6.
  // This is a generic upper bound; specific bounds depend on actual element values.
  // For simplicity, we assume elements fit within `int` and their sum within `int`.
  // A tighter bound would be `requires \forall integer i, j; 0 <= i < R && 0 <= j < C ==> matrix[i*C + j] >= 0;`
  // and `requires (\sum integer j; 0 <= j < C; matrix[i*C + j]) <= INT_MAX;`
  // but Frama-C doesn't directly support \sum in requires for proof.
  // For this problem, we assume the integer types are sufficient.

  assigns matrix[0..(R*C-1)];

  ensures is_sorted_by_row_sum(R, C, matrix);
  ensures is_permutation(R, C, \old(matrix), matrix);
*/
void sort_matrix_by_row_sum(int R, int C, int* matrix) {
    int i, j;
    int temp_row[C]; // Temporary storage for a row during swap

    /*@
      loop invariant 0 <= i <= R;
      loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; i <= l < R ==> sum_row(R, C, matrix, k) <= sum_row(R, C, matrix, l);
      loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; k < l < i ==> sum_row(R, C, matrix, k) <= sum_row(R, C, matrix, l);
      loop invariant is_permutation(R, C, \old(matrix), matrix);
      loop assigns i, j, matrix[0..(R*C-1)], temp_row[0..(C-1)];
      loop variant R - i;
    */
    for (i = 0; i < R - 1; i++) {
        /*@
          loop invariant i <= j <= R;
          loop invariant \forall integer k; i <= k < j ==> sum_row(R, C, matrix, i) <= sum_row(R, C, matrix, k);
          loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; i <= l < R ==> sum_row(R, C, matrix, k) <= sum_row(R, C, matrix, l);
          loop invariant is_permutation(R, C, \old(matrix), matrix);
          loop assigns j, matrix[0..(R*C-1)], temp_row[0..(C-1)];
          loop variant R - j;
        */
        for (j = i + 1; j < R; j++) {
            /*@
              // Check for potential overflow in sum_row calculations if intermediate sums are large.
              // Assuming sum_row itself does not overflow, as per problem setup.
              // This assert is here to guide the prover, not strictly necessary if `sum_row` is axiomatically defined to always return `integer`.
              // assert sum_row(R, C, matrix, i) <= INT_MAX && sum_row(R, C, matrix, j) <= INT_MAX;
            */
            if (sum_row(R, C, matrix, i) > sum_row(R, C, matrix, j)) {
                // Swap rows i and j
                /*@
                  loop invariant 0 <= k <= C;
                  loop invariant \forall integer l; 0 <= l < k ==> temp_row[l] == matrix[i*C + l];
                  loop invariant \forall integer l; 0 <= l < k ==> matrix[i*C + l] == \at(matrix[j*C + l], Pre);
                  loop invariant \forall integer l; 0 <= l < k ==> matrix[j*C + l] == \at(matrix[i*C + l], Pre);
                  loop assigns k, temp_row[0..(C-1)], matrix[i*C..(i*C + C-1)], matrix[j*C..(j*C + C-1)];
                  loop variant C - k;
                */
                for (int k = 0; k < C; k++) {
                    temp_row[k] = matrix[i * C + k];
                    matrix[i * C + k] = matrix[j * C + k];
                    matrix[j * C + k] = temp_row[k];
                }
            }
        }
    }
}
