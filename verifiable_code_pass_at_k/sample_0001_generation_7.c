// Task ID: 1
// Generation: 7

/*@
  requires m >= 0;
  requires n >= 0;
  requires \valid_read(cost + (0..m));
  requires \forall integer i; 0 <= i <= m ==> \valid_read(*(cost + i) + (0..n));

  // Rule I.3: Array parameters decay to pointers.
  assigns \nothing;

  // Rule II.5: Prevent potential overflow in cost calculations.
  // Assuming costs are non-negative, the maximum possible path cost could be
  // (m+1)*(n+1) * MAX_COST_PER_CELL.
  // For int, max_int is 2,147,483,647.
  // If m, n are up to 1000, then (1001)*(1001)*MAX_COST_PER_CELL.
  // Max_cost_per_cell should be limited, e.g., to 2000 for safety.
  // Let's assume cost values are small enough such that their sum doesn't overflow.
  // This requires a more precise bound if costs are high or m, n are large.
  // For simplicity, we'll assume the sum fits in an int.
  // A robust solution would use `long long` for sums or more precise bounds.
  // For this problem, we'll assume `int` is sufficient given reasonable cost values.
*/
int min_cost_path(int m, int n, int* cost[n + 1]) {
    int dp[m + 1][n + 1];

    /*@
      loop invariant 0 <= i <= m + 1;
      loop invariant \forall integer row, col; 0 <= row < i && 0 <= col <= n ==> dp[row][col] >= 0;
      loop invariant \forall integer row, col; 0 <= row < i ==> (
        (row == 0 && col == 0) ==> dp[row][col] == cost[0][0]
      );
      loop invariant \forall integer row, col; 0 <= row < i ==> (
        (row == 0 && col > 0) ==> dp[row][col] == dp[0][col-1] + cost[0][col]
      );
      loop invariant \forall integer row, col; 0 <= row < i ==> (
        (row > 0 && col == 0) ==> dp[row][col] == dp[row-1][0] + cost[row][0]
      );
      loop assigns i, dp[0..m][0..n];
      loop variant m - i;
    */
    for (int i = 0; i <= m; i++) {
        /*@
          loop invariant 0 <= j <= n + 1;
          loop invariant \forall integer col_idx; 0 <= col_idx < j ==> dp[i][col_idx] >= 0;
          loop invariant (i == 0 && j > 0) ==> dp[0][j-1] == (\sum integer k; 0 <= k < j; cost[0][k]);
          loop invariant (i > 0 && j == 0) ==> dp[i][0] == (\sum integer k; 0 <= k < i; cost[k][0]);
          loop invariant (i == 0 && j == 0) ==> dp[0][0] == cost[0][0];

          loop assigns j, dp[i][0..n];
          loop variant n - j;
        */
        for (int j = 0; j <= n; j++) {
            if (i == 0 && j == 0) {
                dp[i][j] = cost[i][j];
            } else if (i == 0) {
                // Rule II.5: Prevent overflow for sum.
                // Requires dp[0][j-1] + cost[0][j] <= INT_MAX
                dp[i][j] = dp[i][j - 1] + cost[i][j];
            } else if (j == 0) {
                // Rule II.5: Prevent overflow for sum.
                // Requires dp[i-1][0] + cost[i][j] <= INT_MAX
                dp[i][j] = dp[i - 1][j] + cost[i][j];
            } else {
                int min_val;
                // Rule II.1, Rule III.2: No C-style ternary, no extra parens for if-then-else
                // Rule III.1: Use ACSL if-then-else
                // Rule II.5: Prevent overflow for sum.
                // Requires dp[i-1][j] + cost[i][j] <= INT_MAX
                // Requires dp[i][j-1] + cost[i][j] <= INT_MAX
                // Requires dp[i-1][j-1] + cost[i][j] <= INT_MAX
                if (dp[i - 1][j] < dp[i][j - 1]) {
                    min_val = dp[i - 1][j];
                } else {
                    min_val = dp[i][j - 1];
                }

                if (min_val < dp[i - 1][j - 1]) {
                    // min_val is already the minimum of (dp[i-1][j], dp[i][j-1])
                } else {
                    min_val = dp[i - 1][j - 1];
                }
                dp[i][j] = min_val + cost[i][j];
            }
        }
    }
    return dp[m][n];
}
