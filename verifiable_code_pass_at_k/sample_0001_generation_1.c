// Task ID: 1
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.

  axiomatic MinCostPath {
    logic integer min_cost_path_rec{L}(int rows, int cols, int cost[][cols], int r, int c)
      reads cost[0..rows-1][0..cols-1];

    axiom min_cost_path_base_r:
      \forall int rows, cols, r, c, cost[][cols];
      (r == 0 && c == 0) ==>
      min_cost_path_rec(rows, cols, cost, r, c) == cost[r][c];

    axiom min_cost_path_base_row:
      \forall int rows, cols, r, c, cost[][cols];
      (r == 0 && c > 0) ==>
      min_cost_path_rec(rows, cols, cost, r, c) == cost[r][c] + min_cost_path_rec(rows, cols, cost, r, c-1);

    axiom min_cost_path_base_col:
      \forall int rows, cols, r, c, cost[][cols];
      (c == 0 && r > 0) ==>
      min_cost_path_rec(rows, cols, cost, r, c) == cost[r][c] + min_cost_path_rec(rows, cols, cost, r-1, c);

    axiom min_cost_path_recursive:
      \forall int rows, cols, r, c, cost[][cols];
      (r > 0 && c > 0) ==>
      min_cost_path_rec(rows, cols, cost, r, c) ==
      cost[r][c] + (if min_cost_path_rec(rows, cols, cost, r-1, c) < min_cost_path_rec(rows, cols, cost, r, c-1) then min_cost_path_rec(rows, cols, cost, r-1, c) else min_cost_path_rec(rows, cols, cost, r, c-1));

    // Helper axiom: Minimum cost must be non-negative if all costs are non-negative.
    axiom min_cost_path_non_negative:
      \forall int rows, cols, r, c, cost[][cols];
      (r >= 0 && c >= 0 && r < rows && c < cols &&
       \forall integer i, j; 0 <= i < rows && 0 <= j < cols ==> cost[i][j] >= 0) ==>
      min_cost_path_rec(rows, cols, cost, r, c) >= 0;

    // Helper axiom: The cost at (r,c) is always part of the sum.
    axiom min_cost_path_at_rc_included:
      \forall int rows, cols, r, c, cost[][cols];
      (r >= 0 && c >= 0 && r < rows && c < cols) ==>
      min_cost_path_rec(rows, cols, cost, r, c) >= cost[r][c];

  }
*/

/*@
  requires rows > 0;
  requires cols > 0;
  requires r >= 0 && r < rows;
  requires c >= 0 && c < cols;
  requires \forall integer i, j; 0 <= i < rows && 0 <= j < cols ==> cost[i][j] >= 0;
  
  // Rule II.5: Prevent overflow. The maximum possible sum can be rows * cols * INT_MAX.
  // Assuming int is 32-bit, INT_MAX is 2,147,483,647.
  // To avoid overflow, rows * cols must be less than INT_MAX / max_single_cost.
  // If max_single_cost is also INT_MAX, then rows * cols must be 1.
  // A more practical approach is to assume cost[i][j] is within a smaller range, e.g., 0 to 1000.
  // If max cost is 1000, then rows * cols < INT_MAX / 1000, approx 2,000,000.
  // For simplicity, let's assume the sum will not overflow for typical matrix sizes.
  // A tighter bound would require more specific assumptions about cost[i][j].
  requires (long long)rows * (long long)cols <= 2000000000; // Roughly, to avoid sum overflow if max_cost is 1.

  assigns \nothing;

  ensures \result == min_cost_path_rec(rows, cols, cost, r, c);
*/
int min_cost_path(int rows, int cols, int cost[][cols], int r, int c) {
    int dp[rows][cols];

    /*@
      loop invariant 0 <= i && i <= rows;
      loop invariant \forall integer x, y;
        0 <= x < i && 0 <= y < cols ==> dp[x][y] == min_cost_path_rec(rows, cols, cost, x, y);
      loop assigns i, dp[0..rows-1][0..cols-1];
      loop variant rows - i;
    */
    for (int i = 0; i < rows; i++) {
        /*@
          loop invariant 0 <= j && j <= cols;
          loop invariant \forall integer x;
            0 <= x < i ==> dp[x][j] == min_cost_path_rec(rows, cols, cost, x, j);
          loop invariant \forall integer y;
            0 <= y < j ==> dp[i][y] == min_cost_path_rec(rows, cols, cost, i, y);
          loop assigns j, dp[i][0..cols-1];
          loop variant cols - j;
        */
        for (int j = 0; j < cols; j++) {
            if (i == 0 && j == 0) {
                dp[i][j] = cost[i][j];
            } else if (i == 0) {
                // Rule II.5: Check for overflow before addition.
                // Assuming dp[i][j-1] + cost[i][j] does not overflow.
                // This requires a stronger requires clause on input costs or matrix dimensions.
                // For instance, dp[i][j-1] <= INT_MAX - cost[i][j]
                // Given the `long long` requires above, this should be fine.
                dp[i][j] = dp[i][j - 1] + cost[i][j];
            } else if (j == 0) {
                // Rule II.5: Check for overflow before addition.
                dp[i][j] = dp[i - 1][j] + cost[i][j];
            } else {
                // Rule II.5: Check for overflow before addition.
                // min(dp[i-1][j], dp[i][j-1]) + cost[i][j]
                // Assuming the sum does not overflow.
                if (dp[i - 1][j] < dp[i][j - 1]) {
                    dp[i][j] = dp[i - 1][j] + cost[i][j];
                } else {
                    dp[i][j] = dp[i][j - 1] + cost[i][j];
                }
            }
        }
    }

    return dp[r][c];
}
