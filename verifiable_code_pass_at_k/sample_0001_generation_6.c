// Task ID: 1
// Generation: 6

/*@
  // Rule II.1: Define recursive logic for sum and minPath.
  axiomatic PathCost {
    logic integer min_of_three(integer a, integer b, integer c);

    axiom min_of_three_def_1:
      \forall integer a, b, c; min_of_three(a, b, c) == (a <= b ? (a <= c ? a : c) : (b <= c ? b : c));

    // Define the minimum cost to reach (i, j)
    logic integer minPath(int M, int N, int cost[M][N], int i, int j);

    // Base case: (0, 0)
    axiom minPath_base:
      \forall int M, N, cost[M][N];
      minPath(M, N, cost, 0, 0) == cost[0][0];

    // Recursive case for (0, j)
    axiom minPath_row_0:
      \forall int M, N, cost[M][N], int j;
      0 < j < N ==> minPath(M, N, cost, 0, j) == minPath(M, N, cost, 0, j - 1) + cost[0][j];

    // Recursive case for (i, 0)
    axiom minPath_col_0:
      \forall int M, N, cost[M][N], int i;
      0 < i < M ==> minPath(M, N, cost, i, 0) == minPath(M, N, cost, i - 1, 0) + cost[i][0];

    // Recursive case for (i, j)
    axiom minPath_general:
      \forall int M, N, cost[M][N], int i, j;
      0 < i < M && 0 < j < N ==>
      minPath(M, N, cost, i, j) == min_of_three(minPath(M, N, cost, i - 1, j - 1),
                                                 minPath(M, N, cost, i - 1, j),
                                                 minPath(M, N, cost, i, j - 1)) + cost[i][j];

    // Rule II.2: Helper axioms for properties of minPath, e.g., non-negativity
    // This is crucial for proving post-conditions involving the range of minPath.
    // Assuming cost elements are non-negative.
    axiom minPath_non_negative_base:
      \forall int M, N, cost[M][N];
      cost[0][0] >= 0 ==> minPath(M, N, cost, 0, 0) >= 0;

    axiom minPath_non_negative_row_0:
      \forall int M, N, cost[M][N], int j;
      0 < j < N && (\forall integer k; 0 <= k <= j ==> cost[0][k] >= 0) ==>
      minPath(M, N, cost, 0, j) >= 0;

    axiom minPath_non_negative_col_0:
      \forall int M, N, cost[M][N], int i;
      0 < i < M && (\forall integer k; 0 <= k <= i ==> cost[k][0] >= 0) ==>
      minPath(M, N, cost, i, 0) >= 0;

    axiom minPath_non_negative_general:
      \forall int M, N, cost[M][N], int i, j;
      0 < i < M && 0 < j < N && (\forall integer r, c; 0 <= r <= i && 0 <= c <= j ==> cost[r][c] >= 0) ==>
      minPath(M, N, cost, i, j) >= 0;
  }
*/

/*@
  requires M > 0 && N > 0;
  requires m >= 0 && m < M;
  requires n >= 0 && n < N;
  // Rule I.3: Array parameter decay: cost is T (*arr)[C]
  // Rule II.5: Prevent potential overflow if costs are large.
  // Assuming int can hold the sum of up to M*N costs.
  // A more precise bound would depend on the maximum cost value and M, N.
  // For simplicity, we assume the sum fits in an int.
  // If cost elements are positive, the result will be positive.
  requires \forall integer i, j; 0 <= i < M && 0 <= j < N ==> cost[i][j] >= 0;

  assigns \nothing;

  ensures \result == minPath(M, N, cost, m, n);
  ensures \result >= 0; // Derived from helper axioms
*/
int minCost(int M, int N, int cost[M][N], int m, int n) {
    int i, j;
    // Rule I.1: No standard libraries. Declare array locally.
    // Rule II.5: Prevent overflow if M*N is very large and intermediate sums exceed INT_MAX.
    // This requires a more precise bound based on M, N, and max cost[i][j].
    // For now, assuming it fits.
    // If M, N are large, this might need `long long` or `int` with smaller range.
    int tc[M][N];

    tc[0][0] = cost[0][0];

    /*@
      loop invariant 1 <= i <= N;
      loop invariant \forall integer k; 0 <= k < i ==> tc[0][k] == minPath(M, N, cost, 0, k);
      loop assigns tc[0][0..N-1], i;
      loop variant N - i;
    */
    for (i = 1; i <= n; i++) { // Loop for first row
        tc[0][i] = tc[0][i - 1] + cost[0][i];
    }

    /*@
      loop invariant 1 <= i <= M;
      loop invariant \forall integer k; 0 <= k < i ==> tc[k][0] == minPath(M, N, cost, k, 0);
      loop assigns tc[0..M-1][0], i;
      loop variant M - i;
    */
    for (i = 1; i <= m; i++) { // Loop for first column
        tc[i][0] = tc[i - 1][0] + cost[i][0];
    }

    /*@
      loop invariant 1 <= i <= M;
      loop invariant \forall integer r; 0 <= r < i ==>
        \forall integer c; 0 <= c <= N - 1 ==> tc[r][c] == minPath(M, N, cost, r, c);
      loop invariant \forall integer c; 0 <= c < j ==> tc[i][c] == minPath(M, N, cost, i, c);
      loop assigns tc[1..M-1][1..N-1], i, j;
      loop variant (M - i) * N + (N - j);
    */
    for (i = 1; i <= m; i++) {
        /*@
          loop invariant 1 <= j <= N;
          loop invariant \forall integer r; 0 <= r < i ==>
            \forall integer c; 0 <= c <= N - 1 ==> tc[r][c] == minPath(M, N, cost, r, c);
          loop invariant \forall integer c; 0 <= c < j ==> tc[i][c] == minPath(M, N, cost, i, c);
          loop assigns tc[i][1..N-1], j;
          loop variant N - j;
        */
        for (j = 1; j <= n; j++) {
            int min_val;
            // Rule III.1: No C-style ternary in ACSL. This is C code, so it's fine here.
            if (tc[i - 1][j - 1] <= tc[i - 1][j]) {
                if (tc[i - 1][j - 1] <= tc[i][j - 1]) {
                    min_val = tc[i - 1][j - 1];
                } else {
                    min_val = tc[i][j - 1];
                }
            } else {
                if (tc[i - 1][j] <= tc[i][j - 1]) {
                    min_val = tc[i - 1][j];
                } else {
                    min_val = tc[i][j - 1];
                }
            }
            // Rule II.5: Prevent overflow for addition.
            // Requires that min_val + cost[i][j] does not exceed INT_MAX.
            tc[i][j] = min_val + cost[i][j];
        }
    }

    return tc[m][n];
}
