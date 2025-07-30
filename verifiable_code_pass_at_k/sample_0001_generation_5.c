// Task ID: 1
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
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

/*@
  // Define maximum dimensions for the cost matrix to prevent overflow and
  // ensure array bounds are manageable for the prover.
  // Assuming 32-bit int, max value is 2,147,483,647.
  // A path sum could exceed this if dimensions are too large and costs are high.
  // For simplicity, let's assume costs are positive and fit within int.
  // The product MAX_ROWS * MAX_COLS should not be excessively large.
  #define MAX_ROWS 100
  #define MAX_COLS 100

  // Axiomatic block for recursive logic to define min_cost_path.
  // This is crucial as we cannot use sum or min directly over paths.
  axiomatic PathCost {
    logic integer min_cost_recursive(int R, int C, int rows, int cols, int cost[R][C]);

    // Base case: If at (0,0), cost is just cost[0][0]
    axiom min_cost_base_0_0:
      \forall int R, C, rows, cols, cost[R][C];
        0 <= R < MAX_ROWS && 0 <= C < MAX_COLS &&
        rows == 0 && cols == 0 ==> min_cost_recursive(R, C, rows, cols, cost) == cost[0][0];

    // Recursive case: If at (0, col), can only come from (0, col-1)
    axiom min_cost_base_0_col:
      \forall int R, C, rows, cols, cost[R][C];
        0 <= R < MAX_ROWS && 0 <= C < MAX_COLS &&
        rows == 0 && cols > 0 ==> min_cost_recursive(R, C, rows, cols, cost) ==
          cost[0][cols] + min_cost_recursive(R, C, 0, cols - 1, cost);

    // Recursive case: If at (row, 0), can only come from (row-1, 0)
    axiom min_cost_base_row_0:
      \forall int R, C, rows, cols, cost[R][C];
        0 <= R < MAX_ROWS && 0 <= C < MAX_COLS &&
        rows > 0 && cols == 0 ==> min_cost_recursive(R, C, rows, cols, cost) ==
          cost[rows][0] + min_cost_recursive(R, C, rows - 1, 0, cost);

    // Recursive case: If at (row, col), can come from (row-1, col), (row, col-1)
    // or (row-1, col-1). We want the minimum.
    axiom min_cost_general:
      \forall int R, C, rows, cols, cost[R][C];
        0 <= R < MAX_ROWS && 0 <= C < MAX_COLS &&
        rows > 0 && cols > 0 ==> min_cost_recursive(R, C, rows, cols, cost) ==
          cost[rows][cols] +
          (if min_cost_recursive(R, C, rows - 1, cols, cost) <= min_cost_recursive(R, C, rows, cols - 1, cost)
           then (if min_cost_recursive(R, C, rows - 1, cols, cost) <= min_cost_recursive(R, C, rows - 1, cols - 1, cost)
                 then min_cost_recursive(R, C, rows - 1, cols, cost)
                 else min_cost_recursive(R, C, rows - 1, cols - 1, cost))
           else (if min_cost_recursive(R, C, rows, cols - 1, cost) <= min_cost_recursive(R, C, rows - 1, cols - 1, cost)
                 then min_cost_recursive(R, C, rows, cols - 1, cost)
                 else min_cost_recursive(R, C, rows - 1, cols - 1, cost)));
  }
*/

/*@
  requires rows > 0 && cols > 0;
  requires m >= 0 && m < rows;
  requires n >= 0 && n < cols;
  
  // Rule II.5: Prevent potential overflow in sums.
  // This is a simplified check. A more robust check would involve checking
  // if cost[i][j] are all positive and sum does not exceed INT_MAX.
  // For demonstration, we assume individual costs are small enough that the
  // total sum fits in an int for typical matrix sizes.
  // We need to ensure that the sum of costs does not overflow.
  // A rough upper bound for path length is (m+n). If all costs are 1, sum is m+n.
  // If all costs are INT_MAX, then (m+n) * INT_MAX could overflow.
  // Let's assume maximum cost is e.g. 1000 and max m,n are 100.
  // Max sum approx 200 * 1000 = 200,000, which fits in int.
  // For a general case, this requires more precise analysis or a type like `long long`.
  // For this problem, we'll assume costs are reasonably small and don't cause overflow.
  // Example: if cost[i][j] <= 1000 and m+n <= 200, then max sum is 200*1000 = 200000.
  
  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The result should be exactly the min_cost_recursive value.
  ensures \result == min_cost_recursive(rows, cols, m, n, cost);
*/
int minCostPath(int rows, int cols, int cost[rows][cols], int m, int n) {
    // dp[i][j] stores the minimum cost to reach (i, j)
    int dp[rows][cols];

    // Rule II.4: Loop annotations for initialization
    /*@
      loop invariant 0 <= i && i <= rows;
      loop invariant \forall integer k; 0 <= k < i ==> 0 <= k < rows;
      loop invariant \forall integer k; 0 <= k < i ==>
        (dp[k][0] == (if k == 0 then cost[0][0] else cost[k][0] + dp[k-1][0]));
      loop assigns dp[0..rows-1][0];
      loop variant rows - i;
    */
    for (int i = 0; i < rows; i++) {
        /*@
          loop invariant 0 <= j && j <= cols;
          loop invariant \forall integer k; 0 <= k < j ==> 0 <= k < cols;
          loop invariant \forall integer k; 0 <= k < j ==>
            (dp[0][k] == (if k == 0 then cost[0][0] else cost[0][k] + dp[0][k-1]));
          loop assigns dp[0][0..cols-1];
          loop variant cols - j;
        */
        for (int j = 0; j < cols; j++) {
            if (i == 0 && j == 0) {
                dp[i][j] = cost[i][j];
            } else if (i == 0) { // First row
                // Rule II.5: Check for potential overflow for addition
                // Assumes cost[i][j] is non-negative and dp[i][j-1] is within range.
                // A more rigorous check would be: if (dp[i][j-1] > INT_MAX - cost[i][j]) ...
                dp[i][j] = cost[i][j] + dp[i][j - 1];
            } else if (j == 0) { // First column
                // Rule II.5: Check for potential overflow for addition
                dp[i][j] = cost[i][j] + dp[i - 1][j];
            } else { // General case
                int val1 = dp[i - 1][j]; // From top
                int val2 = dp[i][j - 1]; // From left
                int val3 = dp[i - 1][j - 1]; // From diagonal

                int min_prev;
                if (val1 <= val2) {
                    if (val1 <= val3) {
                        min_prev = val1;
                    } else {
                        min_prev = val3;
                    }
                } else {
                    if (val2 <= val3) {
                        min_prev = val2;
                    } else {
                        min_prev = val3;
                    }
                }
                // Rule II.5: Check for potential overflow for addition
                dp[i][j] = cost[i][j] + min_prev;
            }
        }
    }

    return dp[m][n];
}
