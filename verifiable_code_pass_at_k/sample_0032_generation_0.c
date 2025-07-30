// Task ID: 32
// Generation: 0

/*@
  // Rule I.1: No standard libraries. ACSL knows INT_MAX.
  // Rule II.5: Prevent overflow for n * n when checking divisibility.
  // 46340 is sqrt(INT_MAX) approximately.
  requires n >= 2 && n <= 46340 * 46340;

  // Rule II.2: Define recursive logic for primality.
  // Rule I.2: Use int for booleans.
  axiom is_prime_def:
    \forall integer x;
      is_prime(x) <==> (x >= 2 && \forall integer i; 2 <= i && i * i <= x ==> x % i != 0);

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like function.
  // The result is the largest prime factor if one exists.
  // If n is prime, the largest prime factor is n itself.
  // If n has no prime factors (i.e., n < 2), the result is 0.
  ensures (\exists integer p;
             is_prime(p) && n % p == 0 &&
             (\forall integer k; k > p && is_prime(k) && n % k == 0 ==> \false)
          ) <==> (\result > 0);
  ensures \result > 0 ==> is_prime(\result) && n % \result == 0;
  ensures \result > 0 ==> \forall integer k; is_prime(k) && n % k == 0 ==> k <= \result;
  ensures n < 2 ==> \result == 0;
  ensures is_prime(n) ==> \result == n;
*/
int largest_prime_factor(int n) {
    if (n < 2) {
        return 0; // No prime factors for numbers less than 2
    }

    int largest_factor = 1;

    // Handle factor 2
    /*@
      loop invariant n_copy % 2 == 0 ==> \forall integer k; 2 <= k < 2 ==> n_copy % k != 0;
      loop invariant n_copy % 2 != 0 ==> \forall integer k; 2 <= k < 2 ==> n_copy % k != 0;
      loop invariant largest_factor == 1; // largest_factor is only set if n_copy is even
      loop invariant n_copy >= 0;
      loop assigns n_copy, largest_factor;
      loop variant n_copy;
    */
    while (n % 2 == 0) {
        largest_factor = 2;
        n /= 2;
    }

    // Now n must be odd. Start checking from 3.
    // Rule II.5: Prevent overflow for i * i
    /*@
      loop invariant i % 2 != 0 || i == 3;
      loop invariant i >= 3;
      loop invariant (n_copy == \old(n_copy)) || (\old(n_copy) % (i-2) == 0 && n_copy == \old(n_copy) / (i-2));
      loop invariant largest_factor >= 1 && largest_factor % 2 == 0; // largest_factor is either 1 or 2 at this point
      loop invariant \forall integer k; (2 < k && k < i && k % 2 != 0) ==> \old(n) % k != 0;
      loop invariant \forall integer k; is_prime(k) && k < i && \old(n)/n % k == 0 ==> k <= largest_factor;
      loop invariant n >= 0;
      loop assigns n, largest_factor, i;
      loop variant n - i;
    */
    for (int i = 3; i * i <= n; i += 2) {
        /*@
          loop invariant i % 2 != 0;
          loop invariant largest_factor >= 1;
          loop invariant \forall integer k; is_prime(k) && k < i && \old(n)/n % k == 0 ==> k <= largest_factor;
          loop invariant n >= 0;
          loop assigns n, largest_factor;
          loop variant n;
        */
        while (n % i == 0) {
            largest_factor = i;
            n /= i;
        }
    }

    // If after all divisions, n is still greater than 1,
    // then the remaining n is a prime factor itself (and the largest one).
    if (n > 1) {
        largest_factor = n;
    }

    return largest_factor;
}
