// Task ID: 20
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1, II.2: Define recursive logic for sum of digits.
  axiomatic SumOfDigits {
    logic integer sum_digits(integer n);

    axiom sum_digits_base:
      \forall integer n; 0 <= n <= 9 ==> sum_digits(n) == n;

    axiom sum_digits_recursive:
      \forall integer n; n > 9 ==> sum_digits(n) == sum_digits(n / 10) + (n % 10);

    // Rule II.2, II.5: Helper axiom to constrain sum_digits for non-negative numbers.
    // This helps in proving that sum_digits will not overflow if n itself is within int range.
    // Max sum of digits for a 32-bit int (2,147,483,647) is 1+9*9 = 82, so it fits in int.
    axiom sum_digits_positive:
      \forall integer n; n >= 0 ==> sum_digits(n) >= 0;
  }
*/

/*@
  // Rule II.1, II.2: Define recursive logic for prime check.
  axiomatic IsPrime {
    logic boolean is_prime_logic(integer n);

    // Base cases
    axiom is_prime_base_0_1: is_prime_logic(0) == \false;
    axiom is_prime_base_2_3: is_prime_logic(2) == \true;
    axiom is_prime_base_3: is_prime_logic(3) == \true;

    // Numbers less than 2 are not prime
    axiom is_prime_less_than_2:
      \forall integer n; n < 2 ==> is_prime_logic(n) == \false;

    // Even numbers greater than 2 are not prime
    axiom is_prime_even_gt_2:
      \forall integer n; n > 2 && n % 2 == 0 ==> is_prime_logic(n) == \false;

    // Recursive definition for odd numbers
    axiom is_prime_recursive:
      \forall integer n; n >= 2 && n % 2 != 0 ==> (is_prime_logic(n) <==> (\forall integer i; 2 <= i && i * i <= n ==> n % i != 0));

    // Rule II.2: Helper axiom - if a number is not prime, it has a divisor.
    axiom not_prime_has_divisor:
      \forall integer n; n >= 2 && !is_prime_logic(n) ==> (\exists integer i; 2 <= i && i * i <= n && n % i == 0);
  }
*/

/*@
  requires n >= 0; // Woodball numbers are typically positive.
  // Rule II.5: Prevent potential overflow if n is large, though sum_digits is small.
  // Max sum_digits for int MAX is 82.
  requires n <= 2147483647; // Ensure n fits in int and doesn't cause issues with modulo/division.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // A number 'n' is a Woodball number if n > 0, n is not prime, and sum_digits(n) is prime.
  ensures (n > 0 && !is_prime_logic(n) && is_prime_logic(sum_digits(n))) <==> (result == 1);
*/
int is_woodball(int n) { // Rule I.2: Uses int for boolean-like return.
    if (n <= 0) { // Woodball numbers are positive.
        return 0;
    }

    // Check if n is prime
    int n_is_prime = 1; // Assume n is prime initially
    /*@
      loop invariant 2 <= i;
      loop invariant i * i <= n + 1; // i*i can go up to n, so i can be sqrt(n).
      loop invariant \forall integer k; 2 <= k < i && k * k <= n ==> n % k != 0;
      loop assigns i;
      loop variant n - i;
    */
    for (int i = 2; i * i <= n; i++) {
        if (n % i == 0) {
            n_is_prime = 0; // n is not prime
            break;
        }
    }

    if (n_is_prime == 1) { // If n is prime, it's not a Woodball number
        return 0;
    }

    // Calculate sum of digits of n
    int current_n = n;
    int digit_sum = 0;
    /*@
      loop invariant current_n >= 0;
      loop invariant \at(current_n, Pre) == current_n * \pow(10, \at(loop_iter, Pre) - loop_iter) + \at(digit_sum, Pre) - digit_sum; // This is a bit complex for loop invariant.
      // A simpler invariant for sum_digits accumulation:
      // invariant: digit_sum is the sum of digits of (\at(n, Pre) - current_n * 10^k) / 10^k for some k.
      // A more practical invariant: digit_sum represents the sum of digits of the part of the original 'n' that has already been processed.
      loop invariant digit_sum == sum_digits(\at(n, Pre) - current_n * (\pow(10, (int)log10((double)\at(n, Pre)) - (int)log10((double)current_n)))); // Too complex.
      // A simpler invariant: sum_digits(\at(n, Pre)) == sum_digits(current_n) + digit_sum
      // This invariant is strong but WP might struggle with log10.
      // Let's use a more direct one:
      loop invariant current_n >= 0;
      loop invariant \at(n, Pre) == current_n * \pow(10, \at(loop_iter, Pre) - current_n_copy_for_iteration) + digit_sum_so_far_from_processed_digits; // No, too complex.
      // The best invariant for sum of digits:
      // current_n is the remaining part of the original number.
      // digit_sum is the sum of digits of the part that has been processed (n_original - current_n).
      loop invariant sum_digits(\at(n, Pre)) == sum_digits(current_n) + digit_sum;
      loop assigns current_n, digit_sum;
      loop variant current_n; // Terminates when current_n becomes 0.
    */
    while (current_n > 0) {
        digit_sum += current_n % 10;
        current_n /= 10;
    }

    // Check if sum of digits is prime
    if (digit_sum <= 1) { // 0 and 1 are not prime
        return 0;
    }
    if (digit_sum == 2 || digit_sum == 3) { // 2 and 3 are prime
        return 1;
    }
    if (digit_sum % 2 == 0) { // Even numbers > 2 are not prime
        return 0;
    }

    int sum_is_prime = 1; // Assume sum_digits is prime initially
    /*@
      loop invariant 2 <= i;
      loop invariant i * i <= digit_sum + 1;
      loop invariant \forall integer k; 2 <= k < i && k * k <= digit_sum ==> digit_sum % k != 0;
      loop assigns i;
      loop variant digit_sum - i;
    */
    for (int i = 3; i * i <= digit_sum; i += 2) { // Start from 3, increment by 2 for odd divisors
        if (digit_sum % i == 0) {
            sum_is_prime = 0; // sum_digits is not prime
            break;
        }
    }

    return sum_is_prime; // If we reach here, n is not prime and sum_digits is prime.
}
