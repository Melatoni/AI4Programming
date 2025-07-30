// Task ID: 24
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans (not applicable directly here, but for return values).
  // Rule I.3: Array pointer decay - applies to `binary_digits`.

  // Rule II.1: Recursive logic for complexity (summation).
  // Rule II.2: Helper axioms.
  // Rule II.3: Ensures clause for boolean-like functions (not applicable directly).
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
    \forall integer base, integer exp;
    exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

  // Rule II.2: Helper axiom to constrain the result of power for positive base.
  axiom power_positive_base_positive_exp:
    \forall integer base, integer exp;
    base > 0 && exp >= 0 ==> power(base, exp) > 0;
}
*/

/*@ axiomatic BinaryToDecimalSum {
  logic integer binary_sum(int* arr, integer from, integer to);

  axiom binary_sum_empty:
    \forall int* arr, integer from, integer to;
    from > to ==> binary_sum(arr, from, to) == 0;

  axiom binary_sum_single:
    \forall int* arr, integer from;
    binary_sum(arr, from, from) == arr[from] * power(2, from);

  axiom binary_sum_rec:
    \forall int* arr, integer from, integer to;
    from <= to ==> binary_sum(arr, from, to) == arr[from] * power(2, from) + binary_sum(arr, from + 1, to);

  // Rule II.2: Helper axiom for the upper bound of the sum.
  // This helps Frama-C reason about the final result not overflowing.
  // Maximum value for an 'int' is INT_MAX (approximately 2*10^9).
  // A 31-bit binary number can be 2^31 - 1.
  // If `n` is max (e.g., 30 for 31 bits), the sum can be 2^31 - 1.
  // This axiom helps connect the sum to the maximum possible value.
  // Requires n to be small enough so that 2^n does not overflow.
  // For `int` (32-bit signed), `n` should be max 30 for 2^n to fit.
  axiom binary_sum_upper_bound:
    \forall int* arr, integer n;
    n >= 0 && n < 31 && (\forall integer k; 0 <= k <= n ==> (arr[k] == 0 || arr[k] == 1)) ==>
    binary_sum(arr, 0, n) <= power(2, n + 1) - 1;
}
*/

/*@
  // Rule I.3: `binary_digits` is an array parameter, decays to a pointer.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // The sum can overflow 'int' if 'n' is too large.
  // For a 32-bit signed int, the maximum value is 2^31 - 1.
  // If n=30, the maximum sum is 2^31 - 1, which fits.
  // If n=31, the maximum sum is 2^32 - 1, which overflows.
  // So, n must be less than 31.
  requires n >= 0 && n < 31;
  requires \valid_read(binary_digits + (0..n));
  requires \forall integer i; 0 <= i <= n ==> (binary_digits[i] == 0 || binary_digits[i] == 1);

  assigns \nothing;

  // Rule II.3: Ensures clause using logical equivalence (implicitly for the return value).
  // The result is exactly the binary sum.
  ensures \result == binary_sum(binary_digits, 0, n);
*/
int binaryToDecimal(int binary_digits[], int n) {
    int decimal_value = 0;
    int power_of_2 = 1;

    /*@
      loop invariant 0 <= i <= n + 1;
      // Rule II.4: Loop invariant for `decimal_value`.
      // The `decimal_value` accumulates the sum of `binary_digits[k] * power(2, k)` for `0 <= k < i`.
      loop invariant decimal_value == binary_sum(binary_digits, 0, i - 1);

      // Rule II.4: Loop invariant for `power_of_2`.
      // `power_of_2` is 2^i.
      loop invariant power_of_2 == power(2, i);

      // Rule II.5: Prevent overflow for `power_of_2`.
      // `power(2, i)` must not exceed `INT_MAX`.
      // Since `i` goes up to `n`, and `n < 31`, `i` will be at most `n`.
      // `power(2, n)` must fit. `power(2, 30)` fits.
      loop invariant power_of_2 <= 1073741824; // 2^30

      // Rule II.5: Prevent overflow for `decimal_value`.
      // `decimal_value + binary_digits[i] * power_of_2` must not overflow.
      // The maximum `decimal_value` is `binary_sum(binary_digits, 0, n)`.
      // We know `binary_sum(arr, 0, n) <= power(2, n + 1) - 1`.
      // Since `n < 31`, `n + 1 <= 31`. `power(2, 31) - 1` fits in `int`.
      // So `decimal_value` will not overflow.
      loop invariant decimal_value <= 2147483647; // INT_MAX

      loop assigns i, decimal_value, power_of_2;

      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 0; i <= n; i++) {
        if (binary_digits[i] == 1) {
            // Rule II.5: Check for potential overflow before addition.
            // This is implicitly handled by the loop invariant `decimal_value <= INT_MAX`
            // and the requirement that `binary_sum` fits within `int`.
            decimal_value += power_of_2;
        }
        // Rule II.5: Check for potential overflow before multiplication.
        // `power_of_2 * 2` must not exceed `INT_MAX`.
        // The loop invariant `power_of_2 <= 2^30` ensures this.
        if (i < n) { // Avoid multiplying on the last iteration unnecessarily.
            power_of_2 *= 2;
        }
    }

    return decimal_value;
}
