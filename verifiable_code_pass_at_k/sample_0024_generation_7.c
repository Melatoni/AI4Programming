// Task ID: 24
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - handled by passing `const int* binary_digits`.

  // Rule II.1: Recursive logic for complexity (summation).
  // Rule II.2: Helper axioms - not strictly needed for this simple summation,
  //            but good practice for more complex recursive definitions.
  // Rule II.3: ensures clause for boolean-like functions - not applicable here,
  //            as the function returns an integer decimal value.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic Power {
  logic integer power(integer base, integer exp);

  axiom power_base:
    \forall integer base; power(base, 0) == 1;

  axiom power_rec:
    \forall integer base, exp;
    exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

  // Helper axiom: power of 2 is always positive for non-negative exponent
  axiom power_of_2_positive:
    \forall integer exp;
    exp >= 0 ==> power(2, exp) >= 1;
}
*/

/*@
  requires num_digits > 0;
  // Prevent overflow for the maximum possible decimal value.
  // For num_digits = 31 (max for signed int), 2^30 - 1 is the max positive.
  // 2^30 approx 10^9. INT_MAX is 2,147,483,647.
  // So, num_digits up to 31 is safe.
  requires num_digits <= 31; // Conservative bound to prevent total_decimal overflow

  // Each digit must be 0 or 1.
  requires \forall integer i; 0 <= i < num_digits ==> (binary_digits[i] == 0 || binary_digits[i] == 1);

  assigns \nothing;

  ensures \result >= 0; // Decimal value is non-negative.

  // The result is the summation of binary_digits[i] * 2^(num_digits - 1 - i)
  // This can be expressed using a recursive logic function for summation.
  // Let's define the logic function for the decimal value.
  ensures \result == sum_binary_to_decimal(binary_digits, num_digits);
*/
int binaryToDecimal(const int* binary_digits, int num_digits) {
    int total_decimal = 0;
    // Current power of 2, starting from 2^0 for the rightmost digit
    int current_power_of_2 = 1;

    /*@
      loop invariant 0 <= i <= num_digits;
      // total_decimal is the sum of (binary_digits[k] * 2^(num_digits - 1 - k)) for k from num_digits-1 down to i
      loop invariant total_decimal == sum_binary_to_decimal_partial(binary_digits, num_digits, i);

      // current_power_of_2 is 2^(num_digits - i)
      loop invariant current_power_of_2 == power(2, num_digits - i);

      loop assigns total_decimal, current_power_of_2, i;
      loop variant i; // Terminates as i decrements to 0
    */
    for (int i = num_digits - 1; i >= 0; i--) {
        // Prevent overflow when adding total_decimal and current_power_of_2
        // Max total_decimal for 31 digits is 2^31 - 1. Max current_power_of_2 is 2^30.
        // sum will not exceed INT_MAX if num_digits <= 31.
        // The individual digit (0 or 1) times current_power_of_2 won't overflow
        // because current_power_of_2 itself is bounded by 2^30.
        if (binary_digits[i] == 1) {
            total_decimal += current_power_of_2;
        }

        // Prevent overflow for current_power_of_2 * 2
        // Max value of current_power_of_2 is 2^30. Next iteration would be 2^31.
        // This is where num_digits <= 31 (so max power is 2^30) is critical.
        // For the next iteration, we need the next power of 2, which is for the next digit to the left.
        // This means we need 2^(num_digits - 1 - (i-1)) = 2^(num_digits - i).
        // So, current_power_of_2 will be multiplied by 2 only if i > 0.
        // The loop is iterating from right to left (LSB to MSB).
        // Let's re-evaluate the power of 2.
        // If i is the index, the power is num_digits - 1 - i.
        // So for i = num_digits - 1, power is 0. current_power_of_2 = 1.
        // For i = num_digits - 2, power is 1. current_power_of_2 = 2.
        // So, after processing binary_digits[i], current_power_of_2 should become 2^(num_digits - 1 - (i-1)) = 2^(num_digits - i).
        // This means current_power_of_2 should be multiplied by 2 in each iteration.
        // We must ensure current_power_of_2 * 2 does not overflow.
        // Since num_digits <= 31, max power is 2^30. 2^30 * 2 = 2^31, which is INT_MIN if signed or would overflow unsigned.
        // However, the sum is what matters. The sum can go up to INT_MAX.
        // The maximum value current_power_of_2 will take is 2^(num_digits-1).
        // If num_digits = 31, max current_power_of_2 = 2^30.
        // The next multiplication current_power_of_2 * 2 would be 2^31, which is problematic.
        // Let's adjust the loop to avoid this.
        // The current_power_of_2 should represent 2^(num_digits - 1 - i_current).
        // It starts at 1 (2^0) for the LSB.
        // The loop should be `i` from `num_digits - 1` down to `0`.
        // `current_power_of_2` represents the weight of `binary_digits[i]`.
        // So `current_power_of_2` starts at 1, and is multiplied by 2 BEFORE the next iteration.

        // Re-design loop: iterate from 0 to num_digits - 1 (MSB to LSB)
        // Or keep current and manage powers differently.
        // Let's try iterating from LSB to MSB.
    }

    // Re-implement with an LSB to MSB approach, which is more natural for powers of 2.
    // The current loop is MSB to LSB.
    // The given loop is processing from MSB (leftmost) to LSB (rightmost) because `i` goes from `num_digits - 1` down to `0`.
    // This implies `binary_digits[num_digits - 1]` is the LSB, `binary_digits[0]` is the MSB.
    // So the problem statement implies `binary_digits` stores digits in MSB-first order.
    // Example: [1, 0, 1, 1] means 1011_2 = 1*2^3 + 0*2^2 + 1*2^1 + 1*2^0.
    // If num_digits=4:
    // i=3: binary_digits[3] (LSB) -> power 2^0
    // i=2: binary_digits[2] -> power 2^1
    // i=1: binary_digits[1] -> power 2^2
    // i=0: binary_digits[0] (MSB) -> power 2^3

    // Let's restart the loop logic.

    total_decimal = 0;
    current_power_of_2 = 1; // Represents 2^j for j = 0, 1, 2...

    /*@
      loop invariant 0 <= i <= num_digits;
      // total_decimal accumulates the sum for digits already processed (from right to left)
      loop invariant total_decimal == sum_binary_to_decimal_right_to_left(binary_digits, num_digits, i);
      // current_power_of_2 is 2^(num_digits - 1 - i)
      loop invariant current_power_of_2 == power(2, num_digits - 1 - i);

      loop assigns total_decimal, current_power_of_2, i;
      loop variant i; // i decrements, ensures termination
    */
    for (int i = num_digits - 1; i >= 0; i--) {
        // Here, binary_digits[i] is the digit corresponding to 2^(num_digits - 1 - i)
        // For i = num_digits - 1, this is 2^0.
        // For i = 0, this is 2^(num_digits - 1).

        if (binary_digits[i] == 1) {
            // Check for potential overflow before addition
            // requires total_decimal <= INT_MAX - current_power_of_2;
            // This is handled by the initial `num_digits <= 31` constraint.
            // If num_digits is 31, the max sum is 2^31-1, which fits in signed int.
            // Current_power_of_2 can be at most 2^30.
            total_decimal += current_power_of_2;
        }

        // Before the next iteration, current_power_of_2 must be updated to 2^(num_digits - 1 - (i-1)) = 2^(num_digits - i)
        // This means current_power_of_2 doubles for the next digit to the left.
        if (i > 0) { // Only multiply if there's a next digit to process to the left
            // Check for potential overflow before multiplication
            // requires current_power_of_2 <= INT_MAX / 2;
            // Max current_power_of_2 can be 2^29 (when i=1, num_digits=31).
            // Then current_power_of_2 * 2 = 2^30, which is safe.
            current_power_of_2 *= 2;
        }
    }

    return total_decimal;
}

/*@ axiomatic BinaryDecimalLogic {
  // Logic function to represent the decimal value of the full binary number
  logic integer sum_binary_to_decimal(const int* binary_digits, integer num_digits);

  axiom sum_binary_to_decimal_base:
    \forall const int* binary_digits, integer num_digits;
    num_digits == 0 ==> sum_binary_to_decimal(binary_digits, num_digits) == 0;

  axiom sum_binary_to_decimal_rec:
    \forall const int* binary_digits, integer num_digits;
    num_digits > 0 ==>
    sum_binary_to_decimal(binary_digits, num_digits) ==
      binary_digits[num_digits - 1] * power(2, 0) +
      sum_binary_to_decimal_rec_helper(binary_digits, num_digits - 1, 1);

  // Helper recursive function for the summation (more natural for loop invariant)
  // This represents the sum of binary_digits[k] * 2^(num_digits - 1 - k) for k from `end_idx - 1` down to `start_idx`.
  // The loop processes from right to left (LSB to MSB).
  // `i` in the loop goes from `num_digits - 1` down to `0`.
  // The sum after `i` is processed is for `binary_digits[num_digits-1]` down to `binary_digits[i]`.
  // The `current_power_of_2` corresponds to `2^(num_digits - 1 - i)`.

  logic integer sum_binary_to_decimal_partial(const int* binary_digits, integer num_digits, integer current_i);

  // Base case: when current_i == num_digits, the sum is 0 (no digits processed yet from the right).
  axiom sum_binary_to_decimal_partial_base:
    \forall const int* binary_digits, integer num_digits;
    sum_binary_to_decimal_partial(binary_digits, num_digits, num_digits) == 0;

  // Recursive step: sum up to current_i is sum up to current_i + 1 plus the value of digit at current_i
  axiom sum_binary_to_decimal_partial_rec:
    \forall const int* binary_digits, integer num_digits, integer current_i;
    0 <= current_i < num_digits ==>
    sum_binary_to_decimal_partial(binary_digits, num_digits, current_i) ==
        binary_digits[current_i] * power(2, num_digits - 1 - current_i) +
        sum_binary_to_decimal_partial(binary_digits, num_digits, current_i + 1);

  // This is the logic that matches the loop's behavior
  logic integer sum_binary_to_decimal_right_to_left(const int* binary_digits, integer num_digits, integer loop_idx);

  // sum for digits from 'loop_idx+1' to 'num_digits-1' (inclusive)
  axiom sum_binary_to_decimal_right_to_left_base:
    \forall const int* binary_digits, integer num_digits;
    loop_idx == -1 ==> sum_binary_to_decimal_right_to_left(binary_digits, num_digits, loop_idx) == 0;

  axiom sum_binary_to_decimal_right_to_left_rec:
    \forall const int* binary_digits, integer num_digits, integer loop_idx;
    0 <= loop_idx < num_digits ==>
    sum_binary_to_decimal_right_to_left(binary_digits, num_digits, loop_idx) ==
      binary_digits[loop_idx] * power(2, num_digits - 1 - loop_idx) +
      sum_binary_to_decimal_right_to_left(binary_digits, num_digits, loop_idx - 1);

  // Helper axiom: The full sum is when loop_idx goes down to -1
  axiom sum_binary_to_decimal_full:
    \forall const int* binary_digits, integer num_digits;
    sum_binary_to_decimal(binary_digits, num_digits) == sum_binary_to_decimal_right_to_left(binary_digits, num_digits, num_digits - 1);

}
*/
