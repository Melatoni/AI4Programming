// Task ID: 24
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans (though not directly for return in this case).
  // Rule I.3: Array pointer decay - not applicable here.

  // Rule II.1: Recursive logic for complexity - not directly needed here; sum is simple enough.
  // Rule II.2: Helper axioms - not directly needed here.
  // Rule II.3: ensures clause for Boolean-like functions - not applicable as return is decimal.
  // Rule II.5: Prevent Runtime Errors (RTE) - power calculation can overflow.
  // The maximum possible decimal value for a 31-bit binary number (max int) is 2^30 - 1.
  // The maximum value for `base` (2^i) can be `2^(length-1)`.
  // If length is 31, base can be 2^30.
  // If `binary[idx]` is 1, `decimal_val` will accumulate `2^idx`.
  // This can exceed INT_MAX if `length` is too large.
  // Assuming `int` is 32-bit signed, max value is 2^31 - 1.
  // A binary number with `length` bits can have a maximum value of `2^length - 1`.
  // To avoid overflow, `2^length - 1` must be less than or equal to `INT_MAX`.
  // So, `length` must be at most 31.
  // If length is 31, the max value is 2^31 - 1, which fits in signed int.
  // However, `base` itself can be `2^(length-1)`. If length is 31, base can be 2^30.
  // The multiplications `binary[idx] * base` and additions `decimal_val + ...` need to fit.
  // If `length` is 31, `base` can be 2^30. `1 * 2^30` fits. Summing these up also fits.
  // So, `length <= 31` is a sufficient constraint for 32-bit signed `int`.

  requires length > 0;
  requires length <= 31; // Max length to prevent overflow for 32-bit signed int.
  requires \valid_read(binary + (0..length-1));

  // Each digit must be 0 or 1.
  requires \forall integer i; 0 <= i < length ==> (binary[i] == 0 || binary[i] == 1);

  assigns \nothing;

  // Define a logic function for power to express the decimal conversion precisely.
  axiomatic Power {
    logic integer power(integer base, integer exp);

    // Base case for power
    axiom power_base:
      \forall integer base; power(base, 0) == 1;

    // Recursive case for power
    axiom power_rec:
      \forall integer base, integer exp;
        exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

    // Helper axiom: power(2, exp) will always be positive
    axiom power_positive:
      \forall integer exp; exp >= 0 ==> power(2, exp) >= 1;
  }

  // Define a logic function to represent the decimal value of the binary number.
  // This uses the power logic function.
  axiomatic BinaryToDecimal {
    logic integer binary_decimal_value(int* binary, integer length);

    // Base case: empty binary number has decimal value 0 (or adjust based on interpretation)
    // For this problem, length > 0, so we can define it recursively from the most significant bit.
    // Or, define it as a sum. A sum can be defined recursively.
    // Let's define the sum recursively from the least significant bit (index 0).

    logic integer sum_of_powers(int* arr, integer idx, integer max_idx);

    // Base case for sum_of_powers
    axiom sum_of_powers_base:
      \forall int* arr, integer max_idx;
        sum_of_powers(arr, max_idx, max_idx) == arr[max_idx] * power(2, max_idx);

    // Recursive case for sum_of_powers
    axiom sum_of_powers_rec:
      \forall int* arr, integer idx, integer max_idx;
        0 <= idx < max_idx ==> sum_of_powers(arr, idx, max_idx) ==
          arr[idx] * power(2, idx) + sum_of_powers(arr, idx + 1, max_idx);

    // The full decimal value is the sum from index 0 to length-1
    axiom binary_decimal_value_def:
      \forall int* binary, integer length;
        length > 0 ==> binary_decimal_value(binary, length) == sum_of_powers(binary, 0, length - 1);
  }

  ensures \result == binary_decimal_value(binary, length);
*/
int binaryToDecimal(int* binary, int length) {
    int decimal_val = 0;
    int base = 1; // Represents 2^i

    /*@
      loop invariant 0 <= i <= length;
      loop invariant base == power(2, i);
      // The `decimal_val` must represent the sum of `binary[k] * 2^k` for `k` from `0` to `i-1`.
      // If i == 0, the sum is empty, so decimal_val is 0.
      loop invariant i == 0 ==> decimal_val == 0;
      loop invariant i > 0 ==> decimal_val == sum_of_powers(binary, 0, i - 1);

      loop assigns i, decimal_val, base;
      loop variant length - i;
    */
    for (int i = 0; i < length; i++) {
        /*@
          // Prevent overflow before multiplication and addition.
          // binary[i] is 0 or 1. If 0, `0 * base` is 0, no overflow.
          // If binary[i] is 1, we add `base` to `decimal_val`.
          // We need `decimal_val + base <= INT_MAX`.
          // Also, `base` itself must not overflow when it becomes `power(2, i+1)`.
          // `base` is `power(2, i)`. The next `base` will be `power(2, i+1)`.
          // In the next iteration, if `i+1 == length`, `base` will be `power(2, length)`.
          // If `length` is 31, `base` would be `power(2, 31)`. This would overflow `int`.
          // However, the loop condition `i < length` means `i` goes up to `length - 1`.
          // So, the maximum value `base` can take *inside* the loop is `power(2, length-1)`.
          // The update `base = base * 2` happens *after* `decimal_val` is updated.
          // So, for `base * 2` to not overflow, `base` must be `INT_MAX / 2` or less.
          // `power(2, length-1)` must be `<= INT_MAX / 2`.
          // If `length-1` is 30, `2^30` is fine. If `length-1` is 31, `2^31` overflows.
          // So `length-1` must be at most 30, meaning `length` must be at most 31. This is already in `requires`.

          // The sum `decimal_val + (binary[i] * base)` must not overflow.
          // `binary[i]` is 0 or 1. So it's `decimal_val + 0` or `decimal_val + base`.
          // We need `decimal_val <= INT_MAX - base`.
          // This is covered by the `length <= 31` constraint which ensures the final result fits.
          // WP should be able to prove this with the overall post-condition.
        */
        if (binary[i] == 1) {
            decimal_val += base;
        }
        // Prevent overflow for the next `base` calculation.
        // `base` will be `power(2, i)`. Next it will be `power(2, i+1)`.
        // This multiplication only happens if `i < length - 1`.
        // So `base * 2` should not overflow if `i < length - 1`.
        // If `i == length - 1`, the loop terminates.
        // The maximum value `i` can take is `length - 1`.
        // So maximum `base` is `power(2, length - 1)`.
        // If `length` is 31, `base` can be `2^30`.
        // `base * 2` would be `2^31`. This would overflow signed int.
        // So we need to ensure `base` is not multiplied by 2 if it would overflow.
        // The `for` loop structure handles this well: `base` is updated, then condition `i < length` is checked.
        // The last `base * 2` will happen when `i == length - 1`.
        // At this point, `base` is `power(2, length - 1)`.
        // `base * 2` would be `power(2, length)`.
        // If `length` is 31, `base * 2` would be `2^31`, which overflows `int`.
        // To avoid this, we can make the `base` calculation conditional,
        // or rely on the `length <= 31` pre-condition.
        // If `length` is exactly 31, then `base` becomes `2^30` in the last iteration.
        // `base = base * 2` would try to compute `2^31`.
        // This is a common pitfall. The `base` update should only happen if `i + 1 < length`.
        if (i < length - 1) { // Rule II.5: Prevent `base` overflow on multiplication.
            base *= 2;
        }
    }
    return decimal_val;
}
