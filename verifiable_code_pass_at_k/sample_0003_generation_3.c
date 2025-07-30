// Task ID: 3
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Not applicable here.

  // Rule II.5: Preconditions to prevent potential overflows or undefined behavior.
  // Maximum value for 'n' such that 'i*i' (where i <= n) doesn't overflow a 32-bit signed int.
  // sqrt(INT_MAX) is approx 46340.
  requires n >= 2 && n <= 46340;

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like function using logical equivalence.
  // The function returns 1 if n is not prime, 0 if n is prime.
  ensures (\exists integer i; 2 <= i <= n / 2 && n % i == 0) <==> (\result == 1);
*/
int is_not_prime(int n) {
    // If n is 0 or 1, it's not prime by definition, but our requires n >= 2 handles this.
    // If n is 2, it's prime. The loop will not execute, and it will return 0. (Correct)
    // If n is 3, it's prime. The loop will not execute, and it will return 0. (Correct)

    /*@
      loop invariant 2 <= i;
      // All integers k from 2 up to i-1 do not divide n.
      loop invariant \forall integer k; 2 <= k < i ==> n % k != 0;
      // i is always less than or equal to n/2 + 1.
      // This is important because the loop condition is i <= n / 2.
      // When i becomes n/2 + 1, the loop terminates.
      loop invariant i <= n / 2 + 1;
      loop assigns i;
      // Rule II.4: Loop variant for termination proof.
      // The distance from the loop upper bound.
      loop variant (n / 2) - i;
    */
    for (int i = 2; i <= n / 2; i++) {
        // Rule II.5: No overflow risk for n % i as n and i are positive.
        if (n % i == 0) {
            return 1; // n is divisible by i, so n is not prime.
        }
    }
    // If no divisor was found, n is prime.
    return 0;
}
