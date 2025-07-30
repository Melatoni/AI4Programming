// Task ID: 3
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Recursive logic for complex properties.
  // Defines a property that a number 'n' has a divisor 'd' such that d*d <= n.
  // This is equivalent to saying 'n' is not prime (if n >= 2).
  axiomatic HasSmallDivisor {
    logic boolean has_small_divisor(integer n, integer current_divisor);

    // Base case: If current_divisor * current_divisor > n, no divisor found up to this point.
    axiom has_small_divisor_base:
      \forall integer n, current_divisor;
        current_divisor * current_divisor > n ==> !has_small_divisor(n, current_divisor);

    // Recursive case 1: If current_divisor divides n, then n has a small divisor.
    axiom has_small_divisor_recursive_found:
      \forall integer n, current_divisor;
        current_divisor * current_divisor <= n && n % current_divisor == 0 ==> has_small_divisor(n, current_divisor);

    // Recursive case 2: If current_divisor does not divide n, check the next divisor.
    axiom has_small_divisor_recursive_continue:
      \forall integer n, current_divisor;
        current_divisor * current_divisor <= n && n % current_divisor != 0 ==> has_small_divisor(n, current_divisor) == has_small_divisor(n, current_divisor + 1);

    // Helper axiom: If a number has a small divisor starting from 2, it means it's composite.
    // This connects the recursive logic to the common definition of non-prime.
    axiom has_small_divisor_implies_composite:
      \forall integer n;
        n >= 2 && has_small_divisor(n, 2) ==> \exists integer d; 2 <= d && d * d <= n && n % d == 0;

    // Helper axiom: If a number is composite, it must have a small divisor starting from 2.
    axiom composite_implies_has_small_divisor:
      \forall integer n;
        n >= 2 && (\exists integer d; 2 <= d && d * d <= n && n % d == 0) ==> has_small_divisor(n, 2);
  }
*/

/*@
  requires n >= 2;
  // Rule II.5: Prevent i*i overflow for 32-bit int.
  // The maximum value for n such that i*i (where i <= sqrt(n)) does not overflow
  // for a 32-bit signed int (max 2,147,483,647) is sqrt(INT_MAX) approx 46340.
  // So, n must be less than or equal to 46340*46340.
  requires n <= 46340 * 46340;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The function returns 1 if n is not prime (composite), 0 otherwise.
  ensures (has_small_divisor(n, 2)) <==> (result == 1);
*/
int is_not_prime(int n) { // Rule I.2: Uses int for boolean-like return.
    /*@
      loop invariant 2 <= i;
      // Rule II.4: Loop invariant for correctness.
      // All numbers k in the range [2, i-1] do not divide n.
      loop invariant \forall integer k; 2 <= k < i ==> n % k != 0;
      loop assigns i;
      // Rule II.4: Loop variant for termination.
      // n - i is not strictly decreasing if i*i can exceed n.
      // A better variant is n - (i*i) or simply n - i, as i strictly increases.
      // i is simpler and sufficient as it increases toward sqrt(n).
      loop variant n - i;
    */
    for (int i = 2; i * i <= n; i++) {
        if (n % i == 0) {
            return 1; // n is divisible by i, so it's not prime.
        }
    }
    return 0; // No divisors found up to sqrt(n), so it's prime.
}
