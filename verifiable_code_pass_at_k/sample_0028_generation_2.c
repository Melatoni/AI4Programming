// Task ID: 28
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.

  // Axiomatic block for factorial logic.
  axiomatic Factorial {
    logic integer factorial(integer n);

    axiom factorial_base:
      factorial(0) == 1;

    axiom factorial_recursive:
      \forall integer n; n > 0 ==> factorial(n) == n * factorial(n - 1);

    // Helper axiom: factorial is always positive for non-negative n.
    axiom factorial_positive:
      \forall integer n; n >= 0 ==> factorial(n) > 0;

    // Helper axiom: factorial is monotonically increasing for n >= 0.
    axiom factorial_monotonic:
      \forall integer n; n >= 0 ==> factorial(n + 1) >= factorial(n);

    // Helper axiom: factorial grows very fast, ensure it fits in int.
    // Max value for 31-bit signed int is 2^31 - 1, which is approx 2 * 10^9.
    // 12! = 479,001,600 fits. 13! = 6,227,020,800 does not.
    // So, we can safely compute factorial up to 12.
    // This implies n should not exceed 12 for direct factorial computation in int.
    axiom factorial_max_value:
      \forall integer n; 0 <= n <= 12 ==> factorial(n) <= 2147483647; // INT_MAX
  }
*/

/*@
  requires n >= 0;
  requires k >= 0;
  requires k <= n;

  // Rule II.5: Prevent overflow for factorial calculations.
  // Since factorial(13) overflows int, n, k, and n-k must be at most 12.
  requires n <= 12;

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions (though this returns int).
  // This ensures clause directly states what the function computes.
  ensures \result == factorial(n) / (factorial(k) * factorial(n - k));
*/
int binomialCoefficient(int n, int k) {
    // Intermediate variables to store factorial results.
    // These need to be int, matching the return type.
    int fact_n = 1;
    int fact_k = 1;
    int fact_n_minus_k = 1;

    // Calculate factorial of n
    /*@
      loop invariant 0 <= i <= n;
      loop invariant fact_n == factorial(i);
      loop assigns fact_n, i;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        fact_n *= (i + 1);
    }

    // Calculate factorial of k
    /*@
      loop invariant 0 <= i <= k;
      loop invariant fact_k == factorial(i);
      loop assigns fact_k, i;
      loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        fact_k *= (i + 1);
    }

    // Calculate factorial of (n - k)
    /*@
      loop invariant 0 <= i <= n - k;
      loop invariant fact_n_minus_k == factorial(i);
      loop assigns fact_n_minus_k, i;
      loop variant (n - k) - i;
    */
    for (int i = 0; i < (n - k); i++) {
        fact_n_minus_k *= (i + 1);
    }

    // Calculate binomial coefficient
    // Rule II.5: Prevent division by zero.
    // By axiom factorial_positive, factorial(k) and factorial(n-k) are > 0.
    // So, fact_k and fact_n_minus_k will be > 0.
    return fact_n / (fact_k * fact_n_minus_k);
}
