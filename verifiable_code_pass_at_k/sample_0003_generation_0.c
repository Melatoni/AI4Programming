// Task ID: 3
// Generation: 0

/*@
  // Rule I.1: No standard libraries are included.
*/

/*@
  // Rule II.1: Defining an axiomatic block for recursive logic.
  // This axiomatic block defines what it means for a number to be "not prime".
  // A number n is not prime if there exists an integer i such that 2 <= i <= n-1 and n % i == 0.
  // For the purpose of optimization, we check up to sqrt(n).

  axiomatic NotPrime {
    logic boolean is_not_prime_logic(integer n);

    // Base case: Numbers less than 2 are not considered prime or non-prime in this context.
    // We define them as not_prime_logic(n) == false for n < 2, as they don't fit the definition.
    axiom is_not_prime_base_0:
      \forall integer n; n < 2 ==> !is_not_prime_logic(n);

    // Recursive definition: n is not prime if it has a divisor starting from 'current_divisor'
    // up to floor(sqrt(n)). This is a helper logic function.
    logic boolean has_divisor_from(integer n, integer current_divisor);

    // Base case for has_divisor_from: If current_divisor * current_divisor > n,
    // we've checked all possible divisors up to sqrt(n) without finding one.
    // Rule II.5: Requires for multiplication to prevent overflow during intermediate calculation.
    // Assuming 32-bit int, n should be <= 46340*46340.
    axiom has_divisor_from_base_no_divisor:
      \forall integer n, current_divisor;
        current_divisor * current_divisor > n ==> !has_divisor_from(n, current_divisor);

    // Recursive case for has_divisor_from: If current_divisor divides n, then n has a divisor.
    axiom has_divisor_from_recursive_found:
      \forall integer n, current_divisor;
        n >= 2 && current_divisor >= 2 && n % current_divisor == 0 ==> has_divisor_from(n, current_divisor);

    // Recursive case for has_divisor_from: If current_divisor does not divide n,
    // check the next divisor (current_divisor + 1).
    // Rule II.5: Requires for multiplication to prevent overflow during intermediate calculation.
    // Also, ensures current_divisor * current_divisor <= n for the next recursive call to be meaningful.
    axiom has_divisor_from_recursive_not_found:
      \forall integer n, current_divisor;
        n >= 2 && current_divisor >= 2 && current_divisor * current_divisor <= n && n % current_divisor != 0 ==>
          has_divisor_from(n, current_divisor) == has_divisor_from(n, current_divisor + 1);

    // Main definition of is_not_prime_logic:
    // A number n (n >= 2) is not prime if it has a divisor starting from 2.
    axiom is_not_prime_recursive:
      \forall integer n; n >= 2 ==> is_not_prime_logic(n) == has_divisor_from(n, 2);

    // Rule II.2: CRITICAL - Helper Axioms (lemmas) for the prover.
    // These axioms help the prover deduce properties that might be too complex for it to infer directly.

    // A positive number n is not prime if it has a divisor d such that 2 <= d <= sqrt(n).
    // This axiom establishes the equivalence between the full definition and the optimized check.
    axiom has_divisor_from_implies_is_not_prime_logic:
      \forall integer n;
        n >= 2 && has_divisor_from(n, 2) ==> is_not_prime_logic(n);

    // If n is not prime, then it must have a divisor in the range [2, sqrt(n)].
    // This is the converse of the above, crucial for the ensures clause.
    axiom is_not_prime_logic_implies_has_divisor_from:
      \forall integer n;
        n >= 2 && is_not_prime_logic(n) ==> has_divisor_from(n, 2);

    // If has_divisor_from(n, start) is true, then there exists an integer k such that
    // start <= k and k*k <= n and n % k == 0. This is the existential form.
    logic integer smallest_divisor(integer n, integer current_divisor);

    // If n has a divisor from current_divisor, then smallest_divisor returns that divisor.
    axiom smallest_divisor_found:
      \forall integer n, current_divisor;
        n >= 2 && current_divisor >= 2 && n % current_divisor == 0 ==>
          smallest_divisor(n, current_divisor) == current_divisor;

    // If n does not have current_divisor as a divisor, check the next one.
    axiom smallest_divisor_not_found:
      \forall integer n, current_divisor;
        n >= 2 && current_divisor >= 2 && current_divisor * current_divisor <= n && n % current_divisor != 0 ==>
          smallest_divisor(n, current_divisor) == smallest_divisor(n, current_divisor + 1);

    // If has_divisor_from(n, current_divisor) is true, then smallest_divisor(n, current_divisor) exists
    // and satisfies the conditions.
    axiom has_divisor_from_exists_smallest_divisor:
      \forall integer n, current_divisor;
        has_divisor_from(n, current_divisor) ==>
          \exists integer k;
            k == smallest_divisor(n, current_divisor) &&
            current_divisor <= k && k * k <= n && n % k == 0;
  }
*/

/*@
  requires n >= 0; // The problem implies checking non-prime for positive integers.
                   // For n < 2, the function will return 0 (false), which is consistent
                   // with them not being considered prime or non-prime.

  // Rule II.5: Prevent overflow for i*i in the loop condition for 32-bit int.
  // INT_MAX is not directly usable here as per Rule I.1, but we know its value.
  // 46340 * 46340 = 2147395600, which is less than 2^31 - 1 (approx 2.147 billion).
  requires n <= 46340 * 46340;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // This links the C function's return value to the ACSL logic definition.
  ensures is_not_prime_logic(n) <==> (\result == 1);
*/
int is_not_prime(int n) { // Rule I.2: Uses int for boolean-like return value.
    if (n < 2) {
        return 0; // Numbers less than 2 are not considered prime or non-prime.
                  // Consistent with !is_not_prime_logic(n) for n < 2.
    }

    /*@
      loop invariant 2 <= i;
      // Rule II.4: Loop invariant capturing the state.
      // All integers k from 2 up to i-1 have been checked and are not divisors of n.
      loop invariant \forall integer k; 2 <= k < i ==> n % k != 0;
      loop invariant i * i <= n + 1; // Ensures i*i doesn't overflow before the loop condition check

      loop assigns i;
      // Rule II.4: A loop variant is mandatory for termination.
      // The value 'n - i' decreases with each iteration and is bounded below by a constant
      // (e.g., n - (sqrt(n) + 1)). A simpler variant is 'n - i' if 'n' is considered fixed,
      // or 'n / i' if 'i' is increasing towards 'sqrt(n)'.
      // A common variant for loops checking up to sqrt(N) is 'n - i*i'.
      // However, 'n - i' works too as 'i' always strictly increases.
      loop variant n - i;
    */
    for (int i = 2; i * i <= n; i++) {
        // Rule II.5: i*i <= n ensures no overflow for the multiplication itself,
        // given n <= 46340*46340.
        if (n % i == 0) {
            return 1; // Corresponds to the 'true' case of the ensures clause (is_not_prime_logic(n) is true).
        }
    }

    // If the loop finishes, no divisor was found up to sqrt(n).
    // This implies n is prime (or not non-prime), so return 0.
    return 0; // Corresponds to the 'false' case of the ensures clause (!is_not_prime_logic(n)).
}
