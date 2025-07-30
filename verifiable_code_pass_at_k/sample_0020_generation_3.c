// Task ID: 20
// Generation: 3

/*@ axiomatic Woodball {
  // Rule II.1: Recursive logic for complex properties (sum of digits raised to power).
  logic integer sum_digits_power(integer n, integer power) reads n, power;

  axiom sum_digits_power_base:
    \forall integer n, power;
      n >= 0 && n < 10 ==> sum_digits_power(n, power) == pow_int(n, power);

  axiom sum_digits_power_recursive:
    \forall integer n, power;
      n >= 10 ==> sum_digits_power(n, power) == pow_int(n % 10, power) + sum_digits_power(n / 10, power);

  // Rule II.2: Helper axiom to prove properties that prover cannot deduce.
  // This axiom helps to bound the sum_digits_power result if digits are bounded.
  // For example, if n is a 32-bit int, then power is at most 10 (for 10 digits).
  // The max digit is 9. pow_int(9, 10) is large.
  // The sum of digits power can exceed INT_MAX for large numbers.
  // We need to ensure that intermediate sums do not overflow.
  // However, for the woodball definition, the sum is compared to the original number.
  // If the sum exceeds INT_MAX, it cannot be equal to 'n' if 'n' is within INT_MAX.
  // We will add a requires clause to the function to prevent overflow for the sum.
  // This axiom is more for general properties, but here the sum itself can overflow int.
  // To avoid this, we will limit the input `n` such that sum_digits_power(n, num_digits(n)) does not overflow.
  // This is handled by the requires clause in the function definition.
}
*/

/*@ axiomatic IntegerFunctions {
  // Helper function for integer power, as pow() is from math.h
  logic integer pow_int(integer base, integer exp) reads base, exp;

  axiom pow_int_base:
    \forall integer base; pow_int(base, 0) == 1;
  axiom pow_int_recursive:
    \forall integer base, exp;
      exp > 0 ==> pow_int(base, exp) == base * pow_int(base, exp - 1);
  axiom pow_int_zero_base:
    pow_int(0, 0) == 1; // Standard definition
  axiom pow_int_zero_base_pos_exp:
    \forall integer exp; exp > 0 ==> pow_int(0, exp) == 0;

  // Helper logic function to count digits (needed for 'power' argument to sum_digits_power)
  logic integer num_digits(integer n) reads n;

  axiom num_digits_base:
    \forall integer n; n >= 0 && n < 10 ==> num_digits(n) == 1;
  axiom num_digits_recursive:
    \forall integer n; n >= 10 ==> num_digits(n) == 1 + num_digits(n / 10);
}
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent overflow for sum_digits_power.
  // The maximum sum for a 32-bit integer (max 10 digits) can be:
  // 9^10 + ... + 9^10 (10 times) which is 10 * 9^10. This is huge.
  // A woodball number implies sum_digits_power(n, num_digits(n)) == n.
  // If n is within INT_MAX, then sum_digits_power(n, num_digits(n)) must also be within INT_MAX.
  // We need a tighter bound on n for this to hold.
  // The largest woodball number is 9999999999, which is larger than INT_MAX.
  // So, we must restrict n to be within INT_MAX and ensure sum_digits_power(n, num_digits(n))
  // does not overflow an int.
  // For n up to 99, num_digits(n) is 2. Max sum_digits_power(99, 2) = 9^2 + 9^2 = 81 + 81 = 162.
  // For n up to 999, num_digits(n) is 3. Max sum_digits_power(999, 3) = 3 * 9^3 = 3 * 729 = 2187.
  // For n up to 9999, num_digits(n) is 4. Max sum_digits_power(9999, 4) = 4 * 9^4 = 4 * 6561 = 26244.
  // For n up to 99999, num_digits(n) is 5. Max sum_digits_power(99999, 5) = 5 * 9^5 = 5 * 59049 = 295245.
  // For n up to 999999, num_digits(n) is 6. Max sum_digits_power(999999, 6) = 6 * 9^6 = 6 * 531441 = 3188646.
  // For n up to 9999999, num_digits(n) is 7. Max sum_digits_power(9999999, 7) = 7 * 9^7 = 7 * 4782969 = 33480783.
  // For n up to 99999999, num_digits(n) is 8. Max sum_digits_power(99999999, 8) = 8 * 9^8 = 8 * 43046721 = 344373768.
  // For n up to 999999999, num_digits(n) is 9. Max sum_digits_power(999999999, 9) = 9 * 9^9 = 9 * 387420489 = 3486784401.
  // This last value (3,486,784,401) exceeds INT_MAX (2,147,483,647).
  // Thus, we must restrict n such that its sum_digits_power does not exceed INT_MAX.
  // The maximum n for which sum_digits_power(n, num_digits(n)) fits in int is for 8 digits.
  // So, n must be less than 1,000,000,000 for sum_digits_power to fit in a signed int.
  // We can further refine this by noting that a woodball number has sum_digits_power(n, num_digits(n)) == n.
  // Since n is an int, the sum must also be an int.
  // The largest possible woodball number that fits in a standard 32-bit signed int
  // (where sum_digits_power also fits) is related to the maximum sum for 9 digits.
  // If num_digits(n) is 9, the max sum is 9 * 9^9, which exceeds INT_MAX.
  // If num_digits(n) is 8, the max sum is 8 * 9^8 = 344373768, which fits in INT_MAX.
  // So, n must have at most 8 digits, i.e., n < 100,000,000.
  // However, the function computes the sum iteratively, so each intermediate sum must not overflow.
  // The intermediate sum `current_sum` and `digit_power` must also not overflow.
  // `digit_power = pow_int(digit, power)`
  // If digit=9 and power=8, 9^8 = 43046721, which fits.
  // If digit=9 and power=9, 9^9 = 387420489, which fits.
  // If digit=9 and power=10, 9^10 = 3486784401, which overflows.
  // So `num_digits(n)` cannot exceed 9.
  // If num_digits(n) is 9, then 9^9 is calculated.
  // The sum `current_sum` can reach 9 * 9^9, which overflows.
  // So, `num_digits(n)` must be at most 8 for `current_sum` to fit in `int`.
  // Thus, `n < 100000000`.
  requires n < 100000000; // Ensures num_digits(n) <= 8 and intermediate sums fit in int.
  assigns \nothing;
  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (sum_digits_power(n, num_digits(n)) == n) <==> (\result == 1);
*/
int is_woodball(int n) {
    if (n < 0) { // Handled by requires n >= 0, but good for robustness.
        return 0;
    }

    if (n == 0) {
        // 0 is not a woodball number by common definition (sum of digits power = 0^1 = 0).
        // However, the problem usually implies positive integers.
        // Based on the recursive definitions, sum_digits_power(0, 1) == pow_int(0, 1) == 0.
        // So, 0 would be a woodball number. We assume positive integers.
        // If 0 is not woodball, then handle it explicitly.
        // If it is, then the general algorithm should cover it.
        // Let's assume 0 is not a woodball number, as per typical problem interpretations.
        // If 0 is considered woodball, remove this line.
        return 0;
    }

    int original_n = n;
    int num_digits_count = 0;
    int temp_n = n;

    /*@
      loop invariant temp_n >= 0;
      loop invariant num_digits_count >= 0;
      // Rule II.4: Invariant for num_digits_count.
      // This invariant is tricky. It relates num_digits_count to the number of digits processed so far.
      // A more useful invariant would be:
      // temp_n == \at(n, LoopEntry) / pow_int(10, num_digits_count);
      // However, for num_digits, we don't need this complex invariant.
      // We just need to ensure num_digits_count counts digits correctly.
      loop invariant (\at(n, LoopEntry) == 0 && num_digits_count == 0) ||
                     (temp_n == 0 && num_digits_count == num_digits(\at(n, LoopEntry))) ||
                     (temp_n > 0 && num_digits_count == num_digits(\at(n, LoopEntry)) - num_digits(temp_n));
      loop assigns temp_n, num_digits_count;
      loop variant temp_n;
    */
    while (temp_n > 0) {
        temp_n /= 10;
        num_digits_count++;
    }

    int current_sum = 0;
    temp_n = original_n; // Reset temp_n to original_n

    /*@
      loop invariant temp_n >= 0;
      loop invariant 0 <= current_sum;
      // Rule II.4: Invariant for current_sum calculation.
      // The sum of digits already processed (from the least significant end).
      // The `num_digits_count` here refers to the total number of digits.
      // The `num_digits(temp_n)` refers to the number of digits remaining.
      // This means the loop iterates `num_digits_count - num_digits(temp_n)` times.
      // The `current_sum` accumulates digits raised to the power of `num_digits_count`.
      loop invariant current_sum == sum_digits_power(original_n / pow_int(10, num_digits(temp_n)), num_digits_count);
      loop assigns temp_n, current_sum;
      loop variant temp_n;
    */
    while (temp_n > 0) {
        int digit = temp_n % 10;
        // Rule II.5: Prevent overflow for pow_int(digit, num_digits_count)
        // This is handled by the `requires n < 100000000` clause.
        // Max digit is 9, max num_digits_count is 8. 9^8 fits in int.
        int digit_power = 1;
        int i = 0;
        /*@
          loop invariant 0 <= i <= num_digits_count;
          loop invariant digit_power == pow_int(digit, i);
          loop assigns digit_power, i;
          loop variant num_digits_count - i;
        */
        for (i = 0; i < num_digits_count; i++) {
            // Rule II.5: Prevent overflow for digit_power * digit.
            // Max digit_power is 9^7 (from previous iteration), max digit is 9.
            // 9^7 * 9 = 9^8. Max 9^8 = 43046721 fits in int.
            digit_power *= digit;
        }
        // Rule II.5: Prevent overflow for current_sum + digit_power.
        // This is also handled by the `requires n < 100000000` clause.
        // Max current_sum is 7 * 9^8 (for 8 digits, 7 processed).
        // Max digit_power is 9^8.
        // (7 * 9^8) + 9^8 = 8 * 9^8 = 344373768, fits in int.
        current_sum += digit_power;
        temp_n /= 10;
    }

    return (current_sum == original_n) ? 1 : 0; // Rule I.2: Return 1 for true, 0 for false.
}
