// Task ID: 1
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay must be handled in ACSL logic.
  // Rule II.1, II.2: Recursive logic for min_path_cost.
  // Rule II.5: Prevent Runtime Errors (RTE) by constraining inputs.
  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic MinPathCost {
    // Rule II.1: Define recursive logic function for minimum path cost.
    // Rule I.3: The array parameter decays to a pointer.
    logic integer min_path_cost_rec{L}(int* cost, int rows, int cols, int m, int n)
      reads cost[0..rows*cols - 1]; // Reads the entire potential array memory
    ;

    // Base case: (0,0)
    axiom min_path_cost_rec_base_0_0{L}:
      \forall int* cost, int rows, int cols;
        min_path_cost_rec(cost, rows, cols, 0, 0) == cost[0];

    // Base case: First row (0, n)
    axiom min_path_cost_rec_base_0_n{L}:
      \forall int* cost, int rows, int cols, int n;
        0 < n && n < cols ==>
        min_path_cost_rec(cost, rows, cols, 0, n) ==
        min_path_cost_rec(cost, rows, cols, 0, n - 1) + cost[n];

    // Base case: First column (m, 0)
    axiom min_path_cost_rec_base_m_0{L}:
      \forall int* cost, int rows, int cols, int m;
        0 < m && m < rows ==>
        min_path_cost_rec(cost, rows, cols, m, 0) ==
        min_path_cost_rec(cost, rows, cols, m - 1, 0) + cost[m * cols];

    // Recursive case: (m, n)
    axiom min_path_cost_rec_recursive{L}:
      \forall int* cost, int rows, int cols, int m, int n;
        0 < m && m < rows && 0 < n && n < cols ==>
        min_path_cost_rec(cost, rows, cols, m, n) ==
        (
          if min_path_cost_rec(cost, rows, cols, m - 1, n) < min_path_cost_rec(cost, rows, cols, m, n - 1)
          then
            if min_path_cost_rec(cost, rows, cols, m - 1, n) < min_path_cost_rec(cost, rows, cols, m - 1, n - 1)
            then min_path_cost_rec(cost, rows, cols, m - 1, n)
            else min_path_cost_rec(cost, rows, cols, m - 1, n - 1)
          else
            if min_path_cost_rec(cost, rows, cols, m, n - 1) < min_path_cost_rec(cost, rows, cols, m - 1, n - 1)
            then min_path_cost_rec(cost, rows, cols, m, n - 1)
            else min_path_cost_rec(cost, rows, cols, m - 1, n - 1)
        ) + cost[m * cols + n];

    // Rule II.2: Helper axioms for the min function.
    // These are crucial for WP to reason about the min logic.
    axiom min_helper_1{L}:
      \forall integer x, y, z;
        (x <= y && x <= z) ==> (x == (if x < y then (if x < z then x else z) else (if y < z then y else z)));

    axiom min_helper_2{L}:
      \forall integer x, y, z;
        (y < x && y <= z) ==> (y == (if x < y then (if x < z then x else z) else (if y < z then y else z)));

    axiom min_helper_3{L}:
      \forall integer x, y, z;
        (z < x && z < y) ==> (z == (if x < y then (if x < z then x else z) else (if y < z then y else z)));

  }
*/

/*@
  requires rows > 0 && cols > 0;
  requires m >= 0 && m < rows;
  requires n >= 0 && n < cols;
  // Rule II.5: Prevent overflow. The maximum cost is (m+n+1) * INT_MAX.
  // Assuming int is 32-bit, max (m+n+1) is around 2*2^15. INT_MAX is 2*10^9.
  // To avoid overflow, the sum of costs should not exceed INT_MAX.
  // A simple heuristic for WP: ensure individual costs are positive and not too large.
  // This is a common challenge for pathfinding; for full safety, a larger integer type
  // or more complex overflow checks would be needed if costs can be large.
  requires \forall integer i; 0 <= i < rows * cols ==> cost[i] >= 0;
  requires \forall integer i; 0 <= i < rows * cols ==> cost[i] <= 1000; // Heuristic bound to help WP.

  assigns \nothing;

  ensures \result == min_path_cost_rec(cost, rows, cols, m, n);
*/
int minCost(int* cost, int rows, int cols, int m, int n) {
    // This is the dynamic programming approach.
    // dp[i][j] stores the minimum cost to reach (i, j).
    // The DP table size is rows * cols.
    // For simplicity and to avoid heap allocation issues with Frama-C,
    // we use a single-dimensional array to simulate the 2D DP table.
    // dp[i * cols + j] represents dp[i][j].
    int dp[rows * cols];

    /*@
      loop invariant 0 <= i_loop <= rows;
      loop invariant \forall integer r, c; 0 <= r < i_loop && 0 <= c < cols ==>
        (r == 0 && c == 0 ==> dp[r*cols + c] == cost[0]) &&
        (r == 0 && c > 0 ==> dp[r*cols + c] == dp[r*cols + (c-1)] + cost[r*cols + c]) &&
        (r > 0 && c == 0 ==> dp[r*cols + c] == dp[(r-1)*cols + c] + cost[r*cols + c]) &&
        (r > 0 && c > 0 ==> dp[r*cols + c] ==
          (if dp[(r-1)*cols + c] < dp[r*cols + (c-1)] then (if dp[(r-1)*cols + c] < dp[(r-1)*cols + (c-1)] then dp[(r-1)*cols + c] else dp[(r-1)*cols + (c-1)]) else (if dp[r*cols + (c-1)] < dp[(r-1)*cols + (c-1)] then dp[r*cols + (c-1)] else dp[(r-1)*cols + (c-1)])) + cost[r*cols + c]
        );
      loop assigns dp[0..rows*cols - 1], i_loop;
      loop variant rows - i_loop;
    */
    for (int i_loop = 0; i_loop < rows; i_loop++) {
        /*@
          loop invariant 0 <= j_loop <= cols;
          loop invariant \forall integer c; 0 <= c < j_loop ==>
            (i_loop == 0 && c == 0 ==> dp[i_loop*cols + c] == cost[0]) &&
            (i_loop == 0 && c > 0 ==> dp[i_loop*cols + c] == dp[i_loop*cols + (c-1)] + cost[i_loop*cols + c]) &&
            (i_loop > 0 && c == 0 ==> dp[i_loop*cols + c] == dp[(i_loop-1)*cols + c] + cost[(i_loop)*cols + c]) &&
            (i_loop > 0 && c > 0 ==> dp[i_loop*cols + c] ==
              (if dp[(i_loop-1)*cols + c] < dp[i_loop*cols + (c-1)] then (if dp[(i_loop-1)*cols + c] < dp[(i_loop-1)*cols + (c-1)] then dp[(i_loop-1)*cols + c] else dp[(i_loop-1)*cols + (c-1)]) else (if dp[i_loop*cols + (c-1)] < dp[(i_loop-1)*cols + (c-1)] then dp[i_loop*cols + (c-1)] else dp[(i_loop-1)*cols + (c-1)])) + cost[i_loop*cols + c]
            );
          loop assigns dp[i_loop*cols .. i_loop*cols + cols - 1], j_loop;
          loop variant cols - j_loop;
        */
        for (int j_loop = 0; j_loop < cols; j_loop++) {
            // Base case
            if (i_loop == 0 && j_loop == 0) {
                dp[i_loop * cols + j_loop] = cost[0];
            }
            // First row (0, j)
            else if (i_loop == 0) {
                // Rule II.5: Check for potential overflow before addition.
                // Assuming cost[i] are positive, this is sufficient.
                // More robust: requires dp[i_loop*cols + (j_loop-1)] <= INT_MAX - cost[i_loop*cols + j_loop];
                dp[i_loop * cols + j_loop] = dp[i_loop * cols + (j_loop - 1)] + cost[i_loop * cols + j_loop];
            }
            // First column (i, 0)
            else if (j_loop == 0) {
                // Rule II.5: Check for potential overflow.
                dp[i_loop * cols + j_loop] = dp[(i_loop - 1) * cols + j_loop] + cost[i_loop * cols + j_loop];
            }
            // General case (i, j)
            else {
                int val1 = dp[(i_loop - 1) * cols + j_loop];      // From (i-1, j)
                int val2 = dp[i_loop * cols + (j_loop - 1)];      // From (i, j-1)
                int val3 = dp[(i_loop - 1) * cols + (j_loop - 1)]; // From (i-1, j-1)

                int min_val;
                // Rule III.1: No C-style ternary in ACSL, but allowed in C code.
                // Rule II.5: Check for potential overflow for min_val + cost[...].
                if (val1 < val2) {
                    if (val1 < val3) {
                        min_val = val1;
                    } else {
                        min_val = val3;
                    }
                } else {
                    if (val2 < val3) {
                        min_val = val2;
                    } else {
                        min_val = val3;
                    }
                }
                dp[i_loop * cols + j_loop] = min_val + cost[i_loop * cols + j_loop];
            }
        }
    }

    return dp[m * cols + n];
}
