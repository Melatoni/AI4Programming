// Task ID: 20
// Generation: 8

/*@
  // Rule II.1: Define recursive logic for sum of digits
  axiomatic SumOfDigits {
  logic integer sum_digits(integer n);

  axiom sum_digits_base:
  \forall integer n; 0 <= n <= 9 ==> sum_digits(n) == n;

  axiom sum_digits_recursive:
  \forall integer n; n > 9 ==> sum_digits(n) == sum_digits(n / 10) + (n % 10);

  // Rule II.2: Helper axiom for sum_digits bounds
  // A number n has sum_digits(n) <= n (for n >= 0)
  axiom sum_digits_le_n:
  \forall integer n; n >= 0 ==> sum_digits(n) <= n;

  // A number n has sum_digits(n) >= 0 (for n >= 0)
  axiom sum_digits_ge_0:
  \forall integer n; n >= 0 ==> sum_digits(n) >= 0;
  }
*/

/*@
  // Rule II.1: Define recursive logic for sum of squares of digits
  axiomatic SumOfSquaresOfDigits {
  logic integer sum_sq_digits(integer n);

  axiom sum_sq_digits_base:
  \forall integer n; 0 <= n <= 9 ==> sum_sq_digits(n) == n * n;

  axiom sum_sq_digits_recursive:
  \forall integer n; n > 9 ==> sum_sq_digits(n) == sum_sq_digits(n / 10) + (n % 10) * (n % 10);

  // Rule II.2: Helper axiom for sum_sq_digits bounds
  // sum_sq_digits(n) >= 0 for n >= 0
  axiom sum_sq_digits_ge_0:
  \forall integer n; n >= 0 ==> sum_sq_digits(n) >= 0;

  // sum_sq_digits(n) <= n * n for n >= 0 (loose upper bound, but useful)
  axiom sum_sq_digits_le_n_sq:
  \forall integer n; n >= 0 ==> sum_sq_digits(n) <= n * n;
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent overflow for sum_sq_digits.
  // Max possible sum of squares for a 9-digit number (2*10^9) would be 9*81 = 729.
  // Max int is 2^31-1. No practical overflow for sum of squares of digits.
  // Adding a loose upper bound for n to prevent intermediate calculations overflow for very large n,
  // although sum_sq_digits itself doesn't cause overflow for int.
  requires n <= 2147483647; // INT_MAX

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return.
  ensures (sum_digits(n) * sum_sq_digits(n) == n) <==> (\result == 1);
*/
int is_woodball(int n) { // Rule I.2: Uses int for boolean
    int sum_d = 0;
    int sum_sq_d = 0;
    int temp_n = n;

    /*@
      loop invariant temp_n >= 0;
      loop invariant sum_d == sum_digits(\at(n, Pre) / (temp_n_at_start / temp_n_at_loop_start)); // This is complex, better to use an axiomatic function
      loop invariant sum_sq_d == sum_sq_digits_tail(\at(n, Pre), temp_n); // Conceptual: for digits already processed
      // More practical loop invariant:
      loop invariant sum_d == sum_digits(\at(n, Pre)) - sum_digits(temp_n);
      loop invariant sum_sq_d == sum_sq_digits(\at(n, Pre)) - sum_sq_digits(temp_n);

      loop assigns sum_d, sum_sq_d, temp_n;
      loop variant temp_n;
    */
    while (temp_n > 0) {
        int digit = temp_n % 10;
        sum_d += digit;
        // Rule II.5: Prevent overflow for digit * digit. Max digit is 9, 9*9=81, no overflow.
        sum_sq_d += digit * digit;
        temp_n /= 10;
    }

    // Rule II.5: Prevent overflow for sum_d * sum_sq_d.
    // Max sum_d for INT_MAX (10 digits) is 9*10 = 90.
    // Max sum_sq_d for INT_MAX (10 digits) is 9*9*10 = 810.
    // 90 * 810 = 72900, which fits in int.
    if ((long long)sum_d * sum_sq_d == n) { // Use long long for intermediate product to be safe
        return 1;
    } else {
        return 0;
    }
}
