// Task ID: 3
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Not applicable here.

  // Rule II.1: No \sum. Not applicable here.
  // Rule II.2: Helper axioms for recursive functions. Not applicable here.

  // Rule II.5: Prevent Runtime Errors (RTE).
  // For `i * i <= n`, `n` must be within a range to prevent `i * i` overflow.
  // The maximum value for `i` will be `sqrt(n)`. If `n` is `INT_MAX`, `sqrt(INT_MAX)` is ~46340.
  // So, `i` can go up to ~46340. `46340 * 46340` fits in `int`.
  // If `n` is `INT_MAX`, then `i * i` could overflow if `i` is large.
  // The largest `i` for `i*i <= n` is `sqrt(n)`. If `n` is `INT_MAX` (2^31-1), `sqrt(n)` is approx 46340.
  // So `i` can be at most 46340. `46340 * 46340` is approx 2.147 * 10^9, which fits in a 32-bit signed int.
  // Thus, `i * i` will not overflow if `n` is within `int` range.
  // However, `n` must be non-negative.
  requires n >= 2;

  // Rule II.3: Ensures clause for boolean-like functions must use logical equivalence.
  // A number `n` is non-prime (composite) if there exists an integer `i` such that `i` divides `n`
  // and `i` is greater than or equal to 2 and `i*i` is less than or equal to `n`.
  ensures (\exists integer i; 2 <= i && i * i <= n && n % i == 0) <==> (result == 1);
  assigns \nothing;
*/
int is_non_prime(int n) {
    /*@
      // Rule III.1: No C-style ternary in ACSL.
      // Rule III.2: No parentheses around if-then-else.
      // Rule III.3: Correct range syntax.
      // Rule III.4: No stray semicolons.

      // Rule II.4: Mandatory loop annotations.
      loop invariant 2 <= i;
      // Loop invariant: All numbers k from 2 up to (but not including) i do not divide n.
      loop invariant \forall integer k; 2 <= k < i ==> n % k != 0;
      loop assigns i;
      // Loop variant: `n - i` is not a good variant because `i` can increase beyond `n`.
      // A better variant is `n / (i + 1)` or `n - i * i` or simply `n - i` if `i` is guaranteed to be less than `n`.
      // Here, `i * i <= n` implies `i <= sqrt(n)`.
      // The variant should be a non-negative integer expression that decreases with each iteration.
      // A simple variant is `(int)sqrt(n) - i`. Since we don't have math functions, `n - i*i` is not always decreasing.
      // A common variant for `for (i = START; P(i); i++)` is `TARGET_VALUE - i`.
      // Here, the loop terminates when `i*i > n`. The largest `i` is `sqrt(n)`.
      // So, `sqrt(n) - i` is a valid variant.
      // Since we can't use `sqrt` in ACSL, we can use `n - i*i` if we can prove it's always non-negative.
      // Or, `n - i` is a valid variant since `i` increases and `i` is bounded (ultimately by `n` or `sqrt(n)`).
      // Let's use `n - i`. Since `i` starts at 2 and increases, and `i*i <= n` implies `i <= n`, `n-i` is a valid variant.
      // No, `n-i` is not always positive. Consider `n=4`, `i=2`. `n-i=2`. Next `i=3`. `i*i=9 > n=4`. Loop terminates.
      // The crucial part is that `i` increases and is bounded.
      // A classic variant for `for (i = 2; i * i <= n; i++)` is `n - i * i`.
      // Let's check `n - i*i`.
      // `i` increases, so `i*i` increases. Thus `n - i*i` decreases.
      // It is non-negative because `i*i <= n` is the loop condition.
      // When `i*i > n`, the loop terminates.
      loop variant n - i * i;
    */
    for (int i = 2; i * i <= n; i++) {
        if (n % i == 0) {
            return 1; // It is non-prime
        }
    }
    return 0; // It is prime
}
