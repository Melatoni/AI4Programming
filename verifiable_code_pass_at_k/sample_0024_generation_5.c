// Task ID: 24
// Generation: 5

/*@
  // Rule I.1: No standard libraries. ACSL constants like INT_MAX are built-in.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: For complex logic, define a recursive logic function.
  // Rule II.2: CRITICAL - Helper Axioms are needed.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax (0..n-1).
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Axiomatic block for recursive logic to calculate powers of 2.
  axiomatic PowerOfTwo {
    logic integer power(integer base, integer exp);

    axiom power_base:
      \forall integer base; power(base, 0) == 1;

    axiom power_recursive:
      \forall integer base, exp;
      exp > 0 ==> power(base, exp) == base * power(base, exp - 1);
  }
*/

/*@
  requires length >= 0;
  requires \forall integer i; 0 <= i < length ==> (binary_digits[i] == 0 || binary_digits[i] == 1);
  // Rule II.5: Prevent overflow. Max possible decimal value for a 31-bit binary number is 2^31 - 1.
  // For `int` (typically 32-bit signed), the maximum value is INT_MAX.
  // The maximum decimal value for a binary number of `length` digits is sum_{i=0}^{length-1} 1 * 2^i = 2^length - 1.
  // So, we need 2^length - 1 <= INT_MAX, which implies 2^length <= INT_MAX + 1.
  // As INT_MAX is 2^31 - 1, INT_MAX + 1 is 2^31. So, length must be <= 31.
  requires length <= 31; // Ensures the result fits in a signed int.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The result is the sum of binary_digits[i] * 2^(length - 1 - i).
  // This can be expressed using a recursive logic function for summation.
  // It's equivalent to \sum_{k=0}^{length-1} binary_digits[length-1-k] * 2^k
  ensures \result == (\sum integer k; 0 <= k < length; binary_digits[length - 1 - k] * power(2, k));
*/
int binary_to_decimal(int* binary_digits, int length) {
    int decimal_value = 0;
    int current_power_of_2 = 1; // Represents 2^0, 2^1, 2^2, ...

    /*@
      loop invariant 0 <= i <= length;
      // decimal_value holds the sum of the processed bits from the right (least significant).
      // The sum is from index `length - 1` down to `length - i`.
      loop invariant decimal_value == (\sum integer k; 0 <= k < i; binary_digits[length - 1 - k] * power(2, k));
      // current_power_of_2 holds 2^i
      loop invariant current_power_of_2 == power(2, i);
      // No overflow for current_power_of_2
      loop invariant current_power_of_2 >= 0;
      // Rule II.5: Prevent overflow for decimal_value accumulation.
      // This invariant ensures that the accumulated decimal_value plus the next term
      // will not exceed INT_MAX.
      // The maximum possible value for remaining terms is 2^length - current_power_of_2.
      // So decimal_value + (2^length - current_power_of_2) <= INT_MAX.
      // Given length <= 31, 2^length is at most 2^31.
      // The loop invariant `decimal_value == (\sum integer k; 0 <= k < i; binary_digits[length - 1 - k] * power(2, k))`
      // and `current_power_of_2 == power(2, i)` combined with `length <= 31`
      // implicitly ensure that `decimal_value <= INT_MAX`.
      // The sum of all terms is guaranteed to fit by the function's `requires length <= 31`.
      // So, we just need to ensure the intermediate product `binary_digits[length - 1 - i] * current_power_of_2`
      // does not overflow before addition. Since binary_digits[x] is 0 or 1, this is `current_power_of_2`.
      // And `current_power_of_2` is guaranteed to be `power(2, i)` which fits given `i < length <= 31`.

      loop assigns i, decimal_value, current_power_of_2;
      // Rule II.4: A loop variant is mandatory for termination.
      loop variant length - i;
    */
    for (int i = 0; i < length; i++) {
        // Process digits from right to left (least significant to most significant)
        if (binary_digits[length - 1 - i] == 1) {
            // Rule II.5: Ensure `decimal_value + current_power_of_2` does not overflow.
            // Since `length <= 31` and `decimal_value` accumulates correctly,
            // the final `decimal_value` will fit. The partial sum also fits.
            // `current_power_of_2` is `2^i`. `decimal_value` is `sum_{k=0}^{i-1} b_{length-1-k} * 2^k`.
            // The max value for `decimal_value + current_power_of_2` is `2^(i+1) - 1`.
            // Since `i < length <= 31`, `i+1 <= 31`. So `2^(i+1) - 1 <= 2^31 - 1 = INT_MAX`.
            // Therefore, no overflow here.
            decimal_value += current_power_of_2;
        }
        // Rule II.5: Ensure `current_power_of_2 * 2` does not overflow.
        // `current_power_of_2` is `2^i`. Next it will be `2^(i+1)`.
        // Since `i < length - 1`, `i+1 < length <= 31`. So `2^(i+1) <= 2^30`.
        // `2^30` fits in a signed `int`.
        if (i < length - 1) { // Avoid overflow on final iteration
            current_power_of_2 *= 2;
        }
    }

    return decimal_value;
}
