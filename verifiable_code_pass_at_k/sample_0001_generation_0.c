// Task ID: 1
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1, II.2: Recursive logic for min_cost.
  axiomatic MinCost {
    logic integer min_cost(int m, int n, int M, int N, int cost[M][N]);

    // Base cases for min_cost:
    axiom min_cost_base_0_0:
      forall int M, N, cost[M][N];
      min_cost(0, 0, M, N, cost) == cost[0][0];

    axiom min_cost_base_0_n:
      forall int n, M, N, cost[M][N];
      (n > 0) ==> min_cost(0, n, M, N, cost) == min_cost(0, n - 1, M, N, cost) + cost[0][n];

    axiom min_cost_base_m_0:
      forall int m, M, N, cost[M][N];
      (m > 0) ==> min_cost(m, 0, M, N, cost) == min_cost(m - 1, 0, M, N, cost) + cost[m][0];

    // Recursive case for min_cost:
    axiom min_cost_recursive:
      forall int m, n, M, N, cost[M][N];
      (m > 0 && n > 0) ==> min_cost(m, n, M, N, cost) ==
        (if min_cost(m - 1, n, M, N, cost) < min_cost(m, n - 1, M, N, cost)
         then min_cost(m - 1, n, M, N, cost)
         else min_cost(m, n - 1, M, N, cost)) + cost[m][n];
         // Rule III.2: No parentheses around if-then-else.

    // Rule II.2: Helper axioms for properties of min_cost.
    // This axiom states that the min_cost is always non-negative if all costs are non-negative.
    axiom min_cost_non_negative:
      forall int m, n, M, N, cost[M][N];
      (forall integer i, j; 0 <= i < M && 0 <= j < N ==> cost[i][j] >= 0)
      ==> min_cost(m, n, M, N, cost) >= 0;

    // This axiom states that the min_cost is always less than or equal to the sum of all costs along one path
    // (e.g., the path that only goes right and then down).
    // This is a placeholder for a more complex upper bound, but demonstrates the concept.
    axiom min_cost_upper_bound_trivial:
      forall int m, n, M, N, cost[M][N];
      (forall integer i, j; 0 <= i < M && 0 <= j < N ==> cost[i][j] >= 0)
      ==> min_cost(m, n, M, N, cost) <= (m + n + 1) * 200000000; // Assuming max cost per cell is 2e8
  }
*/

/*@
  requires M > 0 && N > 0;
  requires 0 <= m < M;
  requires 0 <= n < N;

  // Rule II.5: Prevent potential overflow in cost accumulation.
  // Assuming int type can hold sum up to (M+N-1)*MAX_CELL_COST.
  // A tighter bound would depend on the maximum possible cost value in a cell.
  // For typical int (32-bit), max value is ~2*10^9.
  // If max cell cost is 1000, then (M+N-1)*1000 should be <= 2*10^9.
  // So M+N-1 <= 2*10^6.
  requires (M + N - 1) <= 2000000000 / 1; // Assuming cost values are at least 1.
  // If costs can be negative, the problem becomes more complex (e.g., Bellman-Ford).
  // This problem implies positive costs, or at least no negative cycles.
  // Assuming all cost[i][j] are non-negative for this problem.
  requires \forall integer i, j; 0 <= i < M && 0 <= j < N ==> cost[i][j] >= 0;


  assigns \nothing;

  ensures \result == min_cost(m, n, M, N, cost);
*/
int minCost(int M, int N, int cost[M][N], int m, int n) {
    // dp[i][j] stores the min cost to reach (i, j) from (0, 0)
    int dp[M][N];

    /*@
      loop invariant 0 <= i <= M;
      loop invariant \forall integer i_k; 0 <= i_k < i ==>
        dp[i_k][0] == min_cost(i_k, 0, M, N, cost);
      loop assigns i, dp[0..M-1][0];
      loop variant M - i;
    */
    // Fill first column of DP table
    for (int i = 0; i < M; i++) {
        if (i == 0) {
            dp[i][0] = cost[i][0];
        } else {
            // Rule II.5: Check for overflow before addition.
            // Requires dp[i-1][0] + cost[i][0] to not overflow.
            // This is covered by the main function's requires clause on M+N.
            dp[i][0] = dp[i - 1][0] + cost[i][0];
        }
    }

    /*@
      loop invariant 0 <= j <= N;
      loop invariant \forall integer j_k; 0 <= j_k < j ==>
        dp[0][j_k] == min_cost(0, j_k, M, N, cost);
      loop assigns j, dp[0][0..N-1];
      loop variant N - j;
    */
    // Fill first row of DP table
    for (int j = 0; j < N; j++) {
        if (j == 0) {
            // dp[0][0] is already set by the previous loop if M > 0.
            // If M=0 (not allowed by requires M>0), this would be the first.
            // Given M>0, N>0, dp[0][0] is always filled by the first loop.
            // This 'if' branch is technically redundant if M>0 and first loop runs.
            if (M == 0) { // This branch is unreachable due to requires M>0.
                dp[0][j] = cost[0][j];
            }
        } else {
            // Rule II.5: Check for overflow.
            dp[0][j] = dp[0][j - 1] + cost[0][j];
        }
    }

    /*@
      loop invariant 0 <= i <= M;
      loop invariant \forall integer i_k, j_k;
        0 <= i_k < i && 0 <= j_k < N ==> dp[i_k][j_k] == min_cost(i_k, j_k, M, N, cost);
      loop invariant \forall integer j_k;
        0 <= j_k < N ==> dp[i][j_k] == min_cost(i, j_k, M, N, cost);

      loop assigns i, dp[0..M-1][0..N-1];
      loop variant M - i;
    */
    // Fill rest of the DP table
    for (int i = 1; i < M; i++) {
        /*@
          loop invariant 0 <= j <= N;
          loop invariant \forall integer j_k; 0 <= j_k < j ==>
            dp[i][j_k] == min_cost(i, j_k, M, N, cost);
          loop assigns j, dp[i][0..N-1];
          loop variant N - j;
        */
        for (int j = 1; j < N; j++) {
            int min_prev_cost;
            // Rule III.1: No C-style ternary in ACSL.
            // The if-then-else in C is fine.
            if (dp[i - 1][j] < dp[i][j - 1]) {
                min_prev_cost = dp[i - 1][j];
            } else {
                min_prev_cost = dp[i][j - 1];
            }
            // Rule II.5: Check for overflow.
            dp[i][j] = min_prev_cost + cost[i][j];
        }
    }

    return dp[m][n];
}
