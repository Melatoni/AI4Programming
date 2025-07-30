// Task ID: 36
// Generation: 4

/*@
  // Axiomatic block to define properties related to powers of 10,
  // crucial for the `nth_digit` function.
  axiomatic PowerOf10 {
    logic integer power_of_10(integer exp);

    axiom power_of_10_base:
      power_of_10(0) == 1;

    axiom power_of_10_recursive:
      \forall integer exp; exp > 0 ==> power_of_10(exp) == 10 * power_of_10(exp - 1);

    // Helper axiom: power_of_10 is always positive.
    axiom power_of_10_positive:
      \forall integer exp; exp >= 0 ==> power_of_10(exp) > 0;

    // Helper axiom: For n > 0, 10^n is divisible by 10.
    axiom power_of_10_divisible_by_10:
      \forall integer exp; exp > 0 ==> power_of_10(exp) % 10 == 0;
  }
*/

/*@
  requires num >= 0;
  requires den > 0;
  requires num < den; // Proper fraction
  requires n >= 1; // n-th digit, 1-indexed

  // Prevent overflow for num * 10 in the loop.
  // The maximum value num can take is den - 1.
  // The maximum value for num * 10 is (den - 1) * 10.
  // We need (den - 1) * 10 to fit in an int.
  // INT_MAX is typically 2^31 - 1.
  // So, (den - 1) * 10 <= INT_MAX
  // den - 1 <= INT_MAX / 10
  // den <= (INT_MAX / 10) + 1
  requires den <= (2147483647 / 10) + 1; // Approximately 214748364 + 1 = 214748365

  // Prevent overflow for intermediate_num * 10 in the loop.
  // The value of intermediate_num is always < den.
  // So the same constraint on den applies.

  // The final digit is between 0 and 9.
  ensures \result >= 0 && \result <= 9;
*/
int get_nth_decimal_digit(int num, int den, int n) {
    int intermediate_num = num;
    int current_digit_count = 0;
    int digit_val = 0;

    /*@
      loop invariant current_digit_count >= 0;
      loop invariant current_digit_count <= n;
      loop invariant intermediate_num >= 0;
      loop invariant intermediate_num < den; // Remainder is always less than denominator

      // This invariant is crucial: intermediate_num represents (num * 10^current_digit_count) % den
      // In other words, if the original fraction was N/D, after 'k' iterations,
      // intermediate_num is the numerator for the (k+1)-th digit calculation.
      // This is effectively (N * 10^k) % D.
      loop invariant intermediate_num == (num * power_of_10(current_digit_count)) % den;

      loop assigns intermediate_num, current_digit_count, digit_val;
      loop variant n - current_digit_count;
    */
    while (current_digit_count < n) {
        // Multiply by 10 to shift the next digit into the integer part.
        // Rule II.5: Check for overflow before multiplication.
        // We know intermediate_num < den and den <= (INT_MAX / 10) + 1.
        // So intermediate_num <= (INT_MAX / 10).
        // Therefore, intermediate_num * 10 will not overflow.
        intermediate_num *= 10;

        // Extract the current digit.
        digit_val = intermediate_num / den;

        // Get the new remainder for the next iteration.
        intermediate_num %= den;

        current_digit_count++;
    }

    return digit_val;
}
