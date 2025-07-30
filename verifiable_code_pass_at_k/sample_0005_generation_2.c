// Task ID: 5
// Generation: 2

/*@
  axiomatic DominoWays {
    logic integer domino_ways(integer n);

    axiom domino_ways_0:
      domino_ways(0) == 1;

    axiom domino_ways_1:
      domino_ways(1) == 0;

    axiom domino_ways_2:
      domino_ways(2) == 3;

    axiom domino_ways_n:
      \forall integer n; n >= 3 ==> domino_ways(n) == 4 * domino_ways(n - 2) - domino_ways(n - 4);

    // Helper axioms (Rule II.2) to guide the prover for specific values.
    // These are often needed for recursive definitions where the prover
    // might struggle to unfold to a specific constant value.
    axiom domino_ways_3:
      domino_ways(3) == 0;

    axiom domino_ways_4:
      domino_ways(4) == 11;

    axiom domino_ways_5:
      domino_ways(5) == 0;

    axiom domino_ways_6:
      domino_ways(6) == 41;
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent potential overflow for intermediate calculations if n is large.
  // The maximum value for domino_ways(n) grows exponentially.
  // For n=10, domino_ways(10) = 153.
  // For n=12, domino_ways(12) = 571.
  // For n=14, domino_ways(14) = 2131.
  // For n=16, domino_ways(16) = 7953.
  // For n=18, domino_ways(18) = 29681.
  // For n=20, domino_ways(20) = 110771.
  // For n=22, domino_ways(22) = 413403.
  // For n=24, domino_ways(24) = 1543369.
  // For n=26, domino_ways(26) = 5757961.
  // For n=28, domino_ways(28) = 21491761.
  // For n=30, domino_ways(30) = 80277381.
  // For n=32, domino_ways(32) = 299804243.
  // For n=34, domino_ways(34) = 1118671471.
  // The next value for n=36 would exceed INT_MAX (2,147,483,647).
  requires n <= 34;

  assigns \nothing;

  ensures \result == domino_ways(n);
*/
int solve_domino_3xn(int n) {
    if (n % 2 != 0) {
        return 0; // If n is odd, it's impossible to tile a 3xn board with 2x1 dominoes.
    }

    if (n == 0) {
        return 1;
    }
    if (n == 2) {
        return 3;
    }

    // Using an array to store dynamic programming results.
    // The size `n + 1` ensures `dp[n]` is accessible.
    // Max n is 34, so max array size is 35.
    int dp[35];

    dp[0] = 1;
    dp[2] = 3;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant i % 2 == 0;
      loop invariant i >= 4 ==> dp[i] == 4 * dp[i-2] - dp[i-4];
      loop invariant \forall integer k; (0 <= k < i && k % 2 == 0) ==> dp[k] == domino_ways(k);
      loop assigns dp[4..n];
      loop variant n - i;
    */
    for (int i = 4; i <= n; i += 2) {
        // Rule II.5: Check for potential overflow before multiplication.
        // Assuming dp[i-2] and dp[i-4] are within int range,
        // 4 * dp[i-2] could overflow if dp[i-2] > INT_MAX / 4.
        // Given n <= 34, dp[34] = 1118671471, which fits in int.
        // dp[32] = 299804243. 4 * dp[32] = 1199216972. This also fits.
        dp[i] = 4 * dp[i - 2] - dp[i - 4];
    }

    return dp[n];
}
