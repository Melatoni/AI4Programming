// Task ID: 24
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled for `binary_digits` parameter.
*/

/*@
  // Axiomatic block for recursive logic (Rule II.1, II.2)
  axiomatic BinaryToDecimal {
    logic integer power(integer base, integer exp);

    axiom power_base:
      \forall integer base; power(base, 0) == 1;
    axiom power_recursive:
      \forall integer base, exp;
      exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

    // Helper axiom for power (Rule II.2)
    // Ensures that power(2, k) is always positive for non-negative k
    axiom power_positive:
      \forall integer k; k >= 0 ==> power(2,k) > 0;

    logic integer binary_to_decimal_recursive(int* binary_digits, integer start_idx, integer end_idx);

    axiom binary_to_decimal_base:
      \forall int* binary_digits, integer start_idx, end_idx;
      start_idx > end_idx ==> binary_to_decimal_recursive(binary_digits, start_idx, end_idx) == 0;

    axiom binary_to_decimal_recursive_step:
      \forall int* binary_digits, integer start_idx, end_idx;
      start_idx <= end_idx ==>
        binary_to_decimal_recursive(binary_digits, start_idx, end_idx) ==
          binary_digits[end_idx] * power(2, end_idx - start_idx) +
          binary_to_decimal_recursive(binary_digits, start_idx, end_idx - 1);

    // Helper axiom: if all digits are 0 or 1, the result is non-negative (Rule II.2)
    axiom binary_digits_non_negative:
      \forall int* binary_digits, integer start_idx, end_idx;
        (\forall integer i; start_idx <= i <= end_idx ==> (binary_digits[i] == 0 || binary_digits[i] == 1)) ==>
        binary_to_decimal_recursive(binary_digits, start_idx, end_idx) >= 0;
  }
*/

/*@
  requires num_digits > 0;
  requires \valid_read_range(binary_digits, 0, num_digits - 1);
  // Rule II.5: Prevent potential overflow during conversion.
  // For num_digits = 31 (max for positive int in 2's complement), 2^30 is approx 10^9.
  // For num_digits = 30, 2^29 is approx 5*10^8.
  // INT_MAX is approx 2 * 10^9.
  // The maximum possible value for a 31-digit binary number (all ones) is 2^31 - 1.
  // Since we are returning an `int`, `num_digits` must be constrained to avoid overflow.
  // A 31-bit signed integer can hold up to 2^30 for the most significant bit's place value.
  // So, num_digits should be at most 31 for a standard 32-bit int.
  // If `num_digits` is 31, the highest possible value is 2^31 - 1.
  // If `num_digits` is 32, the highest possible value is 2^32 - 1, which overflows `int`.
  // Thus, num_digits <= 31 is appropriate for a standard 32-bit int.
  requires num_digits <= 31; // Ensures result fits in a signed 32-bit int.

  // All binary digits must be 0 or 1.
  requires \forall integer i; 0 <= i < num_digits ==> (binary_digits[i] == 0 || binary_digits[i] == 1);

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like functions (though this returns int).
  // Here, it defines the mathematical meaning of the result.
  ensures \result == binary_to_decimal_recursive(binary_digits, 0, num_digits - 1);
*/
int binaryToDecimal(int* binary_digits, int num_digits) {
    int decimal_value = 0;
    int power_of_2 = 1; // Corresponds to 2^0

    /*@
      loop invariant 0 <= i <= num_digits;
      loop invariant power_of_2 == power(2, i);
      loop invariant decimal_value == binary_to_decimal_recursive(binary_digits, num_digits - i, num_digits - 1);

      // Rule II.5: Prevent overflow of power_of_2 and decimal_value
      // Note: `INT_MAX` is an ACSL constant.
      loop invariant (i < num_digits ==> power_of_2 <= INT_MAX / 2); // Ensures `power_of_2 * 2` doesn't overflow
      loop invariant (i < num_digits && binary_digits[num_digits - 1 - i] == 1 ==> decimal_value <= INT_MAX - power_of_2); // Ensures `decimal_value + power_of_2` doesn't overflow

      loop assigns i, decimal_value, power_of_2;
      loop variant num_digits - i;
    */
    for (int i = 0; i < num_digits; i++) {
        // The binary digits are processed from right to left (least significant to most significant).
        // binary_digits[num_digits - 1 - i] gets the i-th digit from the right.
        if (binary_digits[num_digits - 1 - i] == 1) {
            decimal_value = decimal_value + power_of_2;
        }
        // Rule II.5: Prevent overflow of power_of_2. Check before multiplication.
        // This check is implicitly covered by the loop invariant `power_of_2 <= INT_MAX / 2`
        // and the `num_digits <= 31` precondition, as for i < 31, power_of_2 will not overflow.
        if (i < num_digits - 1) { // Avoid multiplying power_of_2 unnecessarily on the last iteration
            power_of_2 = power_of_2 * 2;
        }
    }

    return decimal_value;
}
