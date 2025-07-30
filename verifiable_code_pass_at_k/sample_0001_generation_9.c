// Task ID: 1
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms are CRITICAL.
  // Rule II.3: ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.

  axiomatic MinCostPath {
    logic integer min3(integer a, integer b, integer c) =
      if a <= b && a <= c then a
      else if b <= a && b <= c then b
      else c;

    // Rule I.3: Array pointer decay. T arr[R][C] becomes T (*arr)[C].
    logic integer min_cost_path_rec(int R, int C, int (*cost)[C+1], integer m, integer n);

    axiom min_cost_path_base_case_0_0:
      \forall int R, C, integer m, n;
        R >= 0 && C >= 0 && m == 0 && n == 0 ==>
        min_cost_path_rec(R, C, cost, m, n) == cost[m][n];

    axiom min_cost_path_base_case_0_j:
      \forall int R, C, integer m, n;
        R >= 0 && C >= 0 && m == 0 && n > 0 ==>
        min_cost_path_rec(R, C, cost, m, n) == min_cost_path_rec(R, C, cost, m, n-1) + cost[m][n];

    axiom min_cost_path_base_case_i_0:
      \forall int R, C, integer m, n;
        R >= 0 && C >= 0 && m > 0 && n == 0 ==>
        min_cost_path_rec(R, C, cost, m, n) == min_cost_path_rec(R, C, cost, m-1, n) + cost[m][n];

    axiom min_cost_path_recursive_case:
      \forall int R, C, integer m, n;
        R >= 0 && C >= 0 && m > 0 && n > 0 ==>
        min_cost_path_rec(R, C, cost, m, n) ==
          min3(min_cost_path_rec(R, C, cost, m-1, n-1),
               min_cost_path_rec(R, C, cost, m-1, n),
               min_cost_path_rec(R, C, cost, m, n-1)) + cost[m][n];
  }
*/

/*@
  requires rows > 0 && cols > 0;
  requires m >= 0 && m < rows;
  requires n >= 0 && n < cols;
  // Rule II.5: Prevent potential overflow during accumulation.
  // Assuming costs are non-negative, max path length is rows*cols, max cost per cell is INT_MAX.
  // So, ensure (rows * cols) * max_cost_per_cell does not exceed INT_MAX.
  // For simplicity, we assume cost values are small enough or matrix dimensions are not too large.
  // A tighter bound would require knowing the max cost value. Here, a generic bound.
  requires rows * cols <= 2000000; // heuristic to prevent overflow for typical int ranges
  requires \forall integer i, j; 0 <= i < rows && 0 <= j < cols ==> cost[i][j] >= 0;

  assigns \nothing;

  ensures \result == min_cost_path_rec(rows, cols, cost, m, n);
*/
int minCost(int rows, int cols, int (*cost)[cols], int m, int n) {
    int dp[rows][cols];

    /*@
      loop invariant 0 <= i <= rows;
      loop invariant \forall integer r; 0 <= r < i ==>
        dp[r][0] == min_cost_path_rec(rows, cols, cost, r, 0);
      loop assigns i, dp[0..rows-1][0];
      loop variant rows - i;
    */
    for (int i = 0; i < rows; i++) {
        /*@
          loop invariant 0 <= j <= cols;
          loop invariant \forall integer c; 0 <= c < j ==>
             dp[0][c] == min_cost_path_rec(rows, cols, cost, 0, c);
          loop assigns j, dp[0][0..cols-1];
          loop variant cols - j;
        */
        for (int j = 0; j < cols; j++) {
            if (i == 0 && j == 0) {
                dp[i][j] = cost[i][j];
            } else if (i == 0) {
                // Rule II.5: Prevent overflow in addition.
                // dp[0][j-1] + cost[0][j] must not exceed INT_MAX.
                // Assuming positive costs, dp[0][j-1] is non-negative.
                requires (int)\INT_MAX - cost[i][j] >= dp[i][j-1];
                dp[i][j] = dp[i][j-1] + cost[i][j];
            } else if (j == 0) {
                // Rule II.5: Prevent overflow in addition.
                requires (int)\INT_MAX - cost[i][j] >= dp[i-1][j];
                dp[i][j] = dp[i-1][j] + cost[i][j];
            } else {
                // Rule II.5: Prevent overflow in addition.
                // Each term (dp[i-1][j-1], dp[i-1][j], dp[i][j-1]) is a sum of non-negative costs.
                // Their minimum is also non-negative.
                // Ensure min + cost[i][j] does not overflow.
                requires (int)\INT_MAX - cost[i][j] >= dp[i-1][j-1];
                requires (int)\INT_MAX - cost[i][j] >= dp[i-1][j];
                requires (int)\INT_MAX - cost[i][j] >= dp[i][j-1];

                int val1 = dp[i-1][j-1];
                int val2 = dp[i-1][j];
                int val3 = dp[i][j-1];

                int min_val;
                if (val1 <= val2 && val1 <= val3) {
                    min_val = val1;
                } else if (val2 <= val1 && val2 <= val3) {
                    min_val = val2;
                } else {
                    min_val = val3;
                }
                dp[i][j] = min_val + cost[i][j];
            }
        }
    }
    return dp[m][n];
}
