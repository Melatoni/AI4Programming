// Task ID: 24
// Generation: 1

/*@
  // Rule I.2: Represent boolean logic using int. 1 for true, 0 for false.
  // Rule II.1: Recursive logic for complexity (summation).
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.5: Prevent Runtime Errors (RTE) by constraining inputs.
  // The maximum possible value for a 31-bit signed integer is 2^31 - 1.
  // The maximum value a digit can contribute is 1 * 2^30.
  // So, the maximum sum is 2^30 + 2^29 + ... + 2^0 = 2^31 - 1.
  // Thus, `decimal_val` will not overflow if `binary` length is <= 31.
  // We assume int is at least 32-bit.
  // Max length to prevent overflow for a 32-bit signed int result: 31
  requires len >= 0 && len <= 31;
  requires \forall integer k; 0 <= k < len ==> (binary[k] == 0 || binary[k] == 1);

  // Rule I.3: Array parameters decay to pointers.
  axiomatic BinaryToDecimal {
    logic integer power(integer base, integer exp);
    axiom power_base: power(base, 0) == 1;
    axiom power_rec: \forall integer base, exp; exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

    // Helper axiom for power: power(2, exp) is always positive
    axiom power_positive: \forall integer exp; exp >= 0 ==> power(2, exp) >= 1;

    logic integer binary_to_decimal_recursive(int* binary, integer len, integer idx);

    // Base case: empty suffix contributes 0
    axiom binary_to_decimal_recursive_base:
      \forall int* binary, integer len;
      binary_to_decimal_recursive(binary, len, len) == 0;

    // Recursive step: sum the current digit's contribution and the rest
    // The current digit's position (from the right) is len - 1 - idx
    // The power of 2 for the digit at index `idx` is `power(2, len - 1 - idx)`
    axiom binary_to_decimal_recursive_rec:
      \forall int* binary, integer len, integer idx;
      0 <= idx < len ==>
      binary_to_decimal_recursive(binary, len, idx) == binary[idx] * power(2, len - 1 - idx) + binary_to_decimal_recursive(binary, len, idx + 1);

    // Helper axiom: The recursive sum is non-negative
    axiom binary_to_decimal_recursive_non_negative:
      \forall int* binary, integer len, integer idx;
      0 <= idx <= len && (\forall integer k; idx <= k < len ==> (binary[k] == 0 || binary[k] == 1)) ==>
      binary_to_decimal_recursive(binary, len, idx) >= 0;

    // Helper axiom: Upper bound for the recursive sum to avoid overflow
    // This axiom is critical for proving that `decimal_val` will not overflow.
    // Max value for sum of len bits is 2^len - 1.
    // For len <= 31, 2^len - 1 will fit in a signed 32-bit int.
    axiom binary_to_decimal_recursive_upper_bound:
      \forall int* binary, integer len, integer idx;
      0 <= idx <= len && (\forall integer k; idx <= k < len ==> (binary[k] == 0 || binary[k] == 1)) ==>
      binary_to_decimal_recursive(binary, len, idx) <= power(2, len - idx) - 1;
  }
*/
int binary_to_decimal(int* binary, int len) {
    int decimal_val = 0;
    int power_of_2 = 1;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant power_of_2 == power(2, i);
      loop invariant decimal_val == binary_to_decimal_recursive(binary, len, len - i);

      // Helper for loop invariant: decimal_val is non-negative
      loop invariant decimal_val >= 0;
      // Helper for loop invariant: decimal_val is bounded
      loop invariant decimal_val <= power(2, i) - 1;

      loop assigns i, decimal_val, power_of_2;
      loop variant i; // Rule II.4: Loop variant for termination
    */
    for (int i = 0; i < len; i++) {
        // Iterate from the rightmost bit (least significant)
        // Rule I.3: `binary` is a pointer, so `binary[len - 1 - i]` is correct.
        if (binary[len - 1 - i] == 1) {
            // Rule II.5: Prevent overflow for addition.
            // The largest power_of_2 is 2^30 (for len=31, i=30).
            // The largest decimal_val is 2^30 - 1 (for len=31, i=30).
            // Their sum 2^30 + (2^30 - 1) = 2^31 - 1, which fits in a signed 32-bit int.
            // Requires: `power_of_2` does not cause `decimal_val + power_of_2` to overflow.
            // This is guaranteed by the `len <= 31` precondition and the `binary_to_decimal_recursive_upper_bound` axiom.
            decimal_val += power_of_2;
        }

        // Rule II.5: Prevent overflow for multiplication.
        // `power_of_2` goes up to 2^30. `power_of_2 * 2` can be 2^31, which is INT_MIN for signed 32-bit int.
        // So, we must ensure `i < len - 1` when multiplying.
        // The last iteration (i = len - 1) doesn't need this update.
        // If len = 31, i goes up to 30. power_of_2 becomes 2^30.
        // In the next iteration, power_of_2 * 2 would be 2^31.
        // We only update power_of_2 if there's a next iteration.
        if (i < len - 1) {
           power_of_2 *= 2;
        }
    }

    /*@
      // Rule II.3: Ensures clause for boolean-like functions (not directly applicable here as it returns int value).
      // Here, we ensure the result matches the defined logical function.
      ensures \result == binary_to_decimal_recursive(binary, len, 0);
    */
    return decimal_val;
}
