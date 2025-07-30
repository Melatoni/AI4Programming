// Task ID: 32
// Generation: 1

/*@
  // Axiomatic block for recursive logic to define primality
  axiomatic Prime {
    logic boolean is_prime(integer n);

    axiom prime_base_2: is_prime(2) == \true;
    axiom prime_base_3: is_prime(3) == \true;

    // A number n > 3 is prime if it's not divisible by any number k from 2 up to sqrt(n)
    axiom prime_recursive:
      \forall integer n; n > 3 ==> (is_prime(n) <==> (\forall integer k; 2 <= k && k * k <= n ==> n % k != 0));

    // Helper axiom: 1 is not prime
    axiom prime_not_1: is_prime(1) == \false;
    // Helper axiom: 0 and negative numbers are not prime
    axiom prime_not_non_positive: \forall integer n; n <= 0 ==> is_prime(n) == \false;

    // Helper axiom: If a number is prime, it's greater than 1
    axiom prime_gt_1: \forall integer n; is_prime(n) ==> n > 1;
  }
*/

/*@
  requires n > 1; // Largest prime factor is defined for n > 1
  // Prevent overflow for i*i in the loop condition. Max int is 2,147,483,647.
  // sqrt(2,147,483,647) is approx 46340.95. So 46340*46340 is the largest square that fits.
  // If n can be larger than this, its largest prime factor will be n itself if n is prime,
  // or a factor less than or equal to n. The loop `i*i <= n` will correctly handle this
  // as long as `i` itself doesn't overflow.
  // The largest prime factor of a number up to INT_MAX will not exceed INT_MAX.
  // The loop `i*i <= n` means `i` can go up to `sqrt(INT_MAX)`, which is 46340.
  // So `i` itself will not overflow.
  // No specific `requires` for n upper bound beyond `int` max for `i*i` loop condition.

  assigns \nothing;

  ensures \result > 1; // The largest prime factor must be greater than 1
  ensures n % \result == 0; // \result must be a factor of n
  ensures is_prime(\result); // \result must be prime
  // \result must be the largest prime factor: all other prime factors must be smaller
  ensures \forall integer k; k > \result && n % k == 0 ==> !is_prime(k);
*/
int largest_prime_factor(int n) {
    int largest_factor = 1; // Initialize with 1, as 1 is not prime and not a factor we seek

    // Handle factor 2
    /*@
      loop invariant n > 0; // n remains positive
      loop invariant largest_factor == 1 || (largest_factor == 2 && \at(n, Pre) % 2 == 0);
      loop assigns n, largest_factor;
      loop variant n;
    */
    while (n % 2 == 0) {
        largest_factor = 2;
        n = n / 2;
    }

    // Handle odd factors
    // i starts from 3 and increments by 2 (only odd numbers)
    /*@
      loop invariant 3 <= i;
      loop invariant i % 2 != 0; // i is always odd
      loop invariant i * i <= \at(n, LoopCurrent) || \at(n, LoopCurrent) == 1 || \at(n, LoopCurrent) == \at(n, Pre); // Loop condition or n has been fully factored or n is prime
      // All factors found so far are prime and less than or equal to current largest_factor
      loop invariant \forall integer k; 2 <= k < i && \at(n, Pre) % k == 0 && is_prime(k) ==> k <= largest_factor;
      loop invariant largest_factor == 2 || (largest_factor % 2 != 0 && is_prime(largest_factor)); // largest_factor is 2 or an odd prime

      loop assigns n, largest_factor, i;
      loop variant n; // n decreases
    */
    for (int i = 3; i * i <= n; i = i + 2) {
        /*@
          loop invariant n > 0; // n remains positive
          loop invariant i % 2 != 0; // i is odd
          loop invariant \at(n, LoopCurrent) % i != 0 || // if n is not divisible by i, largest_factor is not updated
                         (\at(n, LoopCurrent) % i == 0 && largest_factor == i); // if n is divisible by i, largest_factor becomes i
          loop assigns n, largest_factor;
          loop variant n;
        */
        while (n % i == 0) {
            largest_factor = i;
            n = n / i;
        }
    }

    // If n is still greater than 1, it must be the largest prime factor itself
    // (this handles cases where the original n was a prime number, or the remaining n is prime)
    if (n > 1) {
        largest_factor = n;
    }

    return largest_factor;
}
