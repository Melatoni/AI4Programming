// Task ID: 1
// Generation: 4

/*@
  // Rule II.1, II.2: Define a recursive logic function for minimum path cost.
  // This avoids \min and allows for more complex reasoning.
  axiomatic MinCostPath {
    logic integer min_cost_path_rec(int m, int n, int M, int N, int cost[M][N]);

    // Base case: If at (0,0), cost is cost[0][0]
    axiom min_cost_path_rec_base:
      \forall int M, N, cost[M][N];
      min_cost_path_rec(0, 0, M, N, cost) == cost[0][0];

    // Recursive case for (0, n)
    axiom min_cost_path_rec_row0:
      \forall int m, n, M, N, cost[M][N];
      0 == m && n > 0 ==>
      min_cost_path_rec(m, n, M, N, cost) == min_cost_path_rec(0, n - 1, M, N, cost) + cost[0][n];

    // Recursive case for (m, 0)
    axiom min_cost_path_rec_col0:
      \forall int m, n, M, N, cost[M][N];
      m > 0 && 0 == n ==>
      min_cost_path_rec(m, n, M, N, cost) == min_cost_path_rec(m - 1, 0, M, N, cost) + cost[m][0];

    // Recursive case for (m, n)
    axiom min_cost_path_rec_general:
      \forall int m, n, M, N, cost[M][N];
      m > 0 && n > 0 ==>
      min_cost_path_rec(m, n, M, N, cost) ==
      (if (min_cost_path_rec(m - 1, n, M, N, cost) < min_cost_path_rec(m, n - 1, M, N, cost))
      then min_cost_path_rec(m - 1, n, M, N, cost)
      else min_cost_path_rec(m, n - 1, M, N, cost)) + cost[m][n];
  }
*/

/*@
  requires M > 0 && N > 0;
  requires m >= 0 && m < M;
  requires n >= 0 && n < N;
  // Rule I.3: Array parameter decays to pointer.
  // Rule II.5: Prevent potential overflow. Assume costs are positive and reasonable.
  // This is a placeholder; a more precise bound based on M, N, and max cost value would be needed.
  // For practical purposes, if M, N are small (e.g., < 100), and max cost < 100, then 100*100*100 = 1,000,000 fits int.
  // If costs can be large, a `long long` return type might be needed, or more precise bounds.
  requires \forall integer i, j; 0 <= i < M && 0 <= j < N ==> cost[i][j] >= 0;
  requires (M * N) <= 2000000; // Heuristic to prevent sum overflow for int range.
  requires \forall integer i, j; 0 <= i < M && 0 <= j < N ==> cost[i][j] <= 200; // Heuristic max cost per cell.

  assigns \nothing;

  ensures \result == min_cost_path_rec(m, n, M, N, cost);
*/
int minCost(int m, int n, int M, int N, int cost[M][N]) {
    /*@
      // Rule II.4: Loop invariants for the outer loop
      loop invariant 0 <= i && i <= M;
      loop invariant \forall integer row_idx, col_idx;
        0 <= row_idx < i && 0 <= col_idx < N ==>
        dp[row_idx][col_idx] == min_cost_path_rec(row_idx, col_idx, M, N, cost);
      loop assigns i, j, dp[0..M-1][0..N-1];
      loop variant M - i;
    */
    int dp[M][N]; // Dynamic programming table

    for (int i = 0; i < M; i++) {
        /*@
          // Rule II.4: Loop invariants for the inner loop
          loop invariant 0 <= j && j <= N;
          loop invariant \forall integer col_idx;
            0 <= col_idx < j ==>
            dp[i][col_idx] == min_cost_path_rec(i, col_idx, M, N, cost);
          loop invariant \forall integer row_idx, col_idx;
            0 <= row_idx < i && 0 <= col_idx < N ==>
            dp[row_idx][col_idx] == min_cost_path_rec(row_idx, col_idx, M, N, cost);
          loop assigns j, dp[i][0..N-1];
          loop variant N - j;
        */
        for (int j = 0; j < N; j++) {
            if (i == 0 && j == 0) {
                dp[i][j] = cost[i][j];
            } else if (i == 0) {
                // Rule II.5: Prevent overflow on addition
                /*@ assert (dp[0][j-1] <= INT_MAX - cost[0][j]); */
                dp[i][j] = dp[0][j - 1] + cost[0][j];
            } else if (j == 0) {
                // Rule II.5: Prevent overflow on addition
                /*@ assert (dp[i-1][0] <= INT_MAX - cost[i][0]); */
                dp[i][j] = dp[i - 1][0] + cost[i][0];
            } else {
                int val1 = dp[i - 1][j];
                int val2 = dp[i][j - 1];
                int min_prev_cost;
                // Rule III.2: No parentheses around if-then-else
                // Rule III.1: Use ACSL if-then-else, not C ternary.
                /*@
                  assert min_prev_cost == (if (val1 < val2) then val1 else val2);
                */
                if (val1 < val2) {
                    min_prev_cost = val1;
                } else {
                    min_prev_cost = val2;
                }
                // Rule II.5: Prevent overflow on addition
                /*@ assert (min_prev_cost <= INT_MAX - cost[i][j]); */
                dp[i][j] = min_prev_cost + cost[i][j];
            }
        }
    }
    return dp[m][n];
}
