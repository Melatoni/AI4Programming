// Task ID: 28
// Generation: 1

/*@
    // Axiomatic block for recursive definition of factorial function.
    // Rule II.1: Using recursive logic for complexity (factorial).
    axiomatic Factorial {
        logic integer factorial(integer n);

        // Base case for factorial
        axiom factorial_base:
            factorial(0) == 1;

        // Recursive case for factorial
        axiom factorial_rec:
            \forall integer n; n > 0 ==> factorial(n) == n * factorial(n - 1);

        // Rule II.2: Helper axiom to prove properties of factorial.
        // For non-negative n, factorial(n) is always positive.
        axiom factorial_positive:
            \forall integer n; n >= 0 ==> factorial(n) > 0;

        // Helper axiom to show that factorial is non-decreasing for n >= 0.
        axiom factorial_non_decreasing:
            \forall integer n; n >= 0 ==> factorial(n + 1) >= factorial(n);
    }
*/

/*@
    // Axiomatic block for recursive definition of binomial coefficient.
    // Rule II.1: Using recursive logic for complexity.
    axiomatic BinomialCoefficient {
        logic integer binomial(integer n, integer k);

        // Base cases for binomial coefficient (n choose 0) and (n choose n)
        axiom binomial_base_k_0:
            \forall integer n; n >= 0 ==> binomial(n, 0) == 1;
        axiom binomial_base_k_n:
            \forall integer n; n >= 0 ==> binomial(n, n) == 1;

        // Recursive case for binomial coefficient (Pascal's Identity)
        axiom binomial_rec:
            \forall integer n, k; 0 < k < n ==> binomial(n, k) == binomial(n - 1, k - 1) + binomial(n - 1, k);

        // Helper axiom: (n choose k) is 0 if k > n or k < 0
        axiom binomial_invalid_k:
            \forall integer n, k; (k < 0 || k > n) ==> binomial(n, k) == 0;

        // Helper axiom: Binomial coefficient is symmetric (n choose k) == (n choose n-k)
        axiom binomial_symmetry:
            \forall integer n, k; 0 <= k <= n ==> binomial(n, k) == binomial(n, n - k);

        // Helper axiom: Binomial coefficient can be expressed using factorials
        // This is crucial for connecting the function's implementation to the logic.
        axiom binomial_factorial_def:
            \forall integer n, k; 0 <= k <= n ==> binomial(n, k) == factorial(n) / (factorial(k) * factorial(n - k));

        // Helper axiom: (n choose k) is always non-negative for valid n, k
        axiom binomial_non_negative:
            \forall integer n, k; 0 <= k <= n ==> binomial(n, k) >= 0;
    }
*/

/*@
    requires n >= 0;
    requires k >= 0;
    requires k <= n;

    // Rule II.5: Prevent potential overflow if n is large.
    // This is a heuristic to prevent factorial(n) from overflowing int.
    // Max n for factorial(n) to fit in signed 32-bit int is 12.
    // For binomial coefficient, the value can be larger than factorial(n)
    // but still fit, e.g., (30 choose 15) is ~1.5e8. Max int is ~2e9.
    // A safe upper bound for n for direct factorial calculation is around 12-13.
    // For a more general binomial coefficient, it would require arbitrary precision.
    // Here, we assume the result fits in int, and constrain inputs accordingly.
    // For n=20, (20 choose 10) is 184756, which fits.
    // If we were to calculate factorials directly, n must be small.
    // Since the problem asks for a *python* function and then *C code* for Frama-C,
    // and Frama-C works with 'int', we must assume n and k are small enough
    // for the result to fit in 'int'.
    // A practical limit for 'int' (32-bit signed) is around 2*10^9.
    // (34 choose 17) is approx. 2.3*10^9, so n should ideally be <= 33.
    requires n <= 33; // To ensure result fits in a signed 32-bit int.

    assigns \nothing;

    // Rule II.3: Ensures clause uses logical equivalence for properties.
    // The result should be equal to the logical binomial coefficient.
    ensures \result == binomial(n, k);
*/
int calculate_binomial_coefficient(int n, int k) {
    if (k < 0 || k > n) {
        return 0;
    }
    if (k == 0 || k == n) {
        return 1;
    }
    // Optimize for symmetry: C(n, k) = C(n, n-k)
    if (k > n / 2) {
        k = n - k;
    }

    long long res = 1; // Use long long for intermediate products to prevent overflow

    /*@
        loop invariant 1 <= i <= k + 1;
        loop invariant 1 <= j <= i;
        loop invariant \forall integer x; 1 <= x < i ==> (n - x + 1) % x == 0 || res * (n - x + 1) / x == binomial(n, x);
        loop invariant res == binomial(n, i - 1); // More precise invariant

        loop assigns i, res;
        loop variant k - (i - 1);
    */
    for (int i = 1; i <= k; i++) {
        // This iterative formula calculates C(n, i) from C(n, i-1) using C(n, i) = C(n, i-1) * (n-i+1) / i
        // We ensure that (n - i + 1) * res does not overflow long long before division.
        // We also ensure that the division (res * (n - i + 1)) / i is exact because C(n, i) must be an integer.
        // Frama-C's WP can often prove exact division for binomial coefficients.
        res = res * (n - i + 1) / i;
    }

    // Cast back to int, assuming the final result fits due to the 'requires n <= 33' clause.
    return (int)res;
}
