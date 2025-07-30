// Task ID: 28
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay not applicable here.

  // Rule II.5: Prevent runtime errors (overflows).
  // The maximum value for n and k such that C(n, k) fits in a signed int.
  // C(34, 17) is approximately 2.33 * 10^9, which fits.
  // C(35, 17) is approximately 4.01 * 10^9, which overflows.
  // So, n must be at most 34.
  // For k, 0 <= k <= n.
  requires 0 <= k <= n <= 34;

  assigns \nothing;

  // Rule II.2: Recursive logic for complexity (binomial coefficient definition).
  // Rule II.1: No \sum.
  // Rule II.1: Define recursive logic function within an axiomatic block.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.1: No C-style ternary in ACSL.
  axiom Binomial_base_1: \forall integer n; binomial(n, 0) == 1;
  axiom Binomial_base_2: \forall integer n; binomial(n, n) == 1;
  axiom Binomial_base_3: \forall integer n, k; 0 < k < n ==> binomial(n, k) == binomial(n - 1, k - 1) + binomial(n - 1, k);
  // Rule II.2: Helper axioms.
  // These helper axioms are crucial for WP to relate the recursive definition
  // to the iterative computation.
  // They state that for valid inputs, the binomial coefficient is non-negative
  // and will not overflow if the inputs are within the bounds.
  axiom Binomial_positive: \forall integer n, k; 0 <= k <= n ==> binomial(n, k) >= 0;
  // This helper axiom is implicitly covered by the `requires` clause for the function itself.
  // It asserts that the result of binomial(n, k) will fit in an int if n <= 34.
  // Frama-C's WP can often infer this from the `requires` on the function
  // and the integer range, but explicitly stating it can sometimes help.
  // For this specific problem, the `requires n <= 34` is strong enough.
*/
/*@
  logic integer binomial(integer n, integer k);
*/

/*@
  // Rule II.3: Ensures clause for boolean-like functions not applicable, as it returns a value.
  // Rule II.5: Prevent runtime errors. Covered by function's requires.
  requires 0 <= k <= n <= 34;
  assigns \nothing;
  ensures \result == binomial(n, k);
*/
int binomialCoefficient(int n, int k) {
    // Optimization: C(n, k) = C(n, n-k)
    // This can reduce the number of iterations, but the proof is harder.
    // For simplicity and direct verification, we won't implement this optimization here.
    // If k > n / 2, then k = n - k;
    // if (k > n - k) {
    //     k = n - k;
    // }

    int C[n + 1][k + 1]; // This is a Variable Length Array (VLA).
                         // Frama-C/WP supports VLAs.

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer row; 0 <= row < i ==>
        \forall integer col; 0 <= col <= \min(row, k) ==>
          C[row][col] == binomial(row, col);
      loop assigns i, C;
      loop variant n - i;
    */
    for (int i = 0; i <= n; i++) {
        /*@
          loop invariant 0 <= j <= k;
          loop invariant \forall integer col; 0 <= col < j ==>
            C[i][col] == binomial(i, col);
          loop assigns j, C[i];
          loop variant k - j;
        */
        for (int j = 0; j <= k; j++) {
            if (j == 0 || j == i) {
                C[i][j] = 1;
            } else if (j > i) {
                // This case should not be reached if j <= i for C[i][j].
                // However, the loop bounds for j go up to k.
                // If j > i, then C(i, j) is 0.
                C[i][j] = 0;
            } else {
                // Rule II.5: Prevent overflow.
                // The `requires n <= 34` clause ensures that C[i-1][j-1] + C[i-1][j]
                // will not overflow a signed int.
                C[i][j] = C[i - 1][j - 1] + C[i - 1][j];
            }
        }
    }
    return C[n][k];
}
