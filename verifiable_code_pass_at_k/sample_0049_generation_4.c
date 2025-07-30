// Task ID: 49
// Generation: 4

/*@
  // Rule II.1, II.2: Define a recursive logic function for extracting elements.
  // This function describes the property of the resulting array.
  axiomatic GetColumn {
    // Column elements: column j of a matrix M up to row i-1
    logic integer column_elements(int R, int C, int M[R][C], int col, int i, int k);

    axiom column_elements_base:
      \forall int R, C, M[R][C], col, k;
        col >= 0 && col < C ==> column_elements(R, C, M, col, 0, k) == k; // Arbitrary value for empty sequence

    axiom column_elements_recursive:
      \forall int R, C, M[R][C], col, i, k;
        0 < i && i <= R && col >= 0 && col < C ==>
        column_elements(R, C, M, col, i, k) == M[i-1][col]; // We only care about the last element for this problem
                                                            // For full sequence, it would be a concatenation or similar.
                                                            // For this problem, the 'k' parameter is not strictly needed
                                                            // to represent the extracted elements themselves, but rather
                                                            // to allow the recursive definition to be well-formed.
                                                            // The ensures clause will specify the actual values.

    // Helper axiom: All elements in the extracted column are within the bounds of `int`.
    // This isn't strictly necessary for this problem, but shows how helper axioms work.
    // Rule II.2: Helper Axioms
    axiom column_elements_range:
      \forall int R, C, M[R][C], col, i;
        0 <= i && i <= R && col >= 0 && col < C ==>
        \forall integer k;
          (column_elements(R, C, M, col, i, k) >= INT_MIN && column_elements(R, C, M, col, i, k) <= INT_MAX);
  }
*/

/*@
  requires R > 0;
  requires C > 0;
  requires col_idx >= 0 && col_idx < C;
  // Rule I.3: Array pointer decay - M is int (*M)[C], result is int *.
  assigns result[0..R-1];

  // Rule II.3: Ensures clause for function behavior.
  // It states that for each row 'i', the element in 'result[i]'
  // must be equal to the element M[i][col_idx].
  ensures \forall integer i; 0 <= i < R ==> result[i] == M[i][col_idx];
  // Using the axiomatic function to describe the property of the output array.
  // This ensures that the result array contains the specified column elements.
  // The column_elements function effectively "extracts" the column in the logic.
  ensures \forall integer i; 0 <= i < R ==> result[i] == column_elements(R, C, M, col_idx, i + 1, 0);
*/
void extract_column(int R, int C, int M[R][C], int col_idx, int result[R]) {
    /*@
      loop invariant 0 <= i <= R;
      // Rule II.4: Invariant states that elements processed so far are correct.
      loop invariant \forall integer k; 0 <= k < i ==> result[k] == M[k][col_idx];
      loop assigns i, result[0..R-1];
      // Rule II.4: Loop variant for termination.
      loop variant R - i;
    */
    for (int i = 0; i < R; i++) {
        result[i] = M[i][col_idx];
    }
}
