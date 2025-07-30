// Task ID: 24
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in formal parameters.
  // Rule II.1: Recursive logic for complexity (if needed).
  // Rule II.2: Helper axioms (if needed).
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.

  // Axiomatic block to define power function for use in ACSL.
  // This is needed because there's no built-in power operator for integers in ACSL.
  axiomatic Power {
    logic integer power(integer base, integer exp);

    axiom power_base_zero:
      \forall integer exp; exp > 0 ==> power(0, exp) == 0;
    axiom power_exponent_zero:
      \forall integer base; power(base, 0) == 1;
    axiom power_recursive:
      \forall integer base, exp; exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

    // Helper axiom for power, useful for proving bounds
    axiom power_positive:
      \forall integer base, exp; base >= 0 && exp >= 0 ==> power(base, exp) >= 0;
  }

  requires 0 <= size;
  requires size <= 30; // Max size to prevent overflow for 2^size for int (2^30 < INT_MAX)
  // Each digit must be 0 or 1
  requires \forall integer i; 0 <= i < size ==> (binary_digits[i] == 0 || binary_digits[i] == 1);

  assigns \nothing;

  // Define a recursive logic function to calculate the decimal value of a binary number.
  // This avoids \sum and provides a verifiable way to express the sum.
  logic integer binary_to_decimal_logic(int* binary_digits, integer start, integer end);

  axiom binary_to_decimal_base:
    \forall int* binary_digits, integer start;
      binary_to_decimal_logic(binary_digits, start, start) == 0; // Empty range contributes 0

  axiom binary_to_decimal_recursive:
    \forall int* binary_digits, integer start, end;
      start < end ==>
      binary_to_decimal_logic(binary_digits, start, end) ==
      binary_digits[end - 1] * power(2, end - 1 - start) + binary_to_decimal_logic(binary_digits, start, end - 1);

  // Helper axiom: if all digits are 0 or 1, the result is non-negative
  axiom binary_to_decimal_non_negative:
    \forall int* binary_digits, integer start, end;
      (\forall integer i; start <= i < end ==> (binary_digits[i] == 0 || binary_digits[i] == 1)) ==>
      binary_to_decimal_logic(binary_digits, start, end) >= 0;

  // The ensures clause states that the result is equal to the logical decimal value.
  ensures \result == binary_to_decimal_logic(binary_digits, 0, size);
  // Also ensure the result is non-negative
  ensures \result >= 0;
*/
int binaryToDecimal(int* binary_digits, int size) {
    int decimal_value = 0;
    int power_of_2 = 1;

    /*@
      loop invariant 0 <= i <= size;
      // decimal_value holds the decimal equivalent of binary_digits[size-1]...binary_digits[size-1-i+1]
      loop invariant (i == 0 ==> decimal_value == 0);
      loop invariant (i > 0 ==> decimal_value == binary_to_decimal_logic(binary_digits, size - i, size));
      // power_of_2 holds 2^(i)
      loop invariant power_of_2 == power(2, i);
      // All digits processed so far were 0 or 1
      loop invariant \forall integer k; size - i <= k < size ==> (binary_digits[k] == 0 || binary_digits[k] == 1);
      // Ensure no overflow for power_of_2
      loop invariant power_of_2 >= 0;
      loop invariant power_of_2 <= 1 << (size); // Upper bound for power_of_2
      // Ensure no overflow for decimal_value
      loop invariant decimal_value <= 1 << (size); // Upper bound for decimal_value

      loop assigns i, decimal_value, power_of_2;
      loop variant i; // i decreases from size to 0
    */
    for (int i = 0; i < size; i++) {
        // Check for potential overflow before multiplication and addition
        // decimal_value + binary_digits[size - 1 - i] * power_of_2
        // Max value of binary_digits[size - 1 - i] is 1.
        // So we need to check if decimal_value + power_of_2 > INT_MAX
        // Since size <= 30, max result is 2^30 - 1, which fits in int.
        // We ensure this by the outer requires size <= 30.

        if (binary_digits[size - 1 - i] == 1) {
            decimal_value = decimal_value + power_of_2;
        }
        // Check for potential overflow for power_of_2 * 2
        // Max power is 2^(size-1) in the loop, then 2^size after update.
        // Since size <= 30, 2^30 fits in int.
        // We ensure this by the outer requires size <= 30.
        if (i < size - 1) { // Avoid multiplying power_of_2 in the last iteration
            power_of_2 = power_of_2 * 2;
        }
    }

    return decimal_value;
}
