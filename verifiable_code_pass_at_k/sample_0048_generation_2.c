// Task ID: 48
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.5: Prevent overflow for 32-bit int.
  // The maximum value for `x` is INT_MAX (2^31 - 1).
  // The loop iterates up to 31 times.
  // The expression `1 << i` can overflow if `i` is 31 and `1` is treated as signed.
  // We specify `1U` to ensure an unsigned shift.
  // The result `odd_bits` can accumulate up to `INT_MAX`.
  // The maximum sum of odd powers of 2 up to 30: 2^1 + 2^3 + ... + 2^29.
  // This sum is roughly (2^30 - 1)/3, which fits in an int.
  // So, no specific `requires` for `x` beyond its range for `int`.
*/

/*@
  assigns \nothing; // The function only computes and returns a value.

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The result `res` should be a number where all odd bits are set to 1,
  // and all even bits are set to 0.
  ensures (\forall integer k; 0 <= k < 31 ==> ((\result >> k) & 1) == (if k % 2 == 1 then 1 else 0));
*/
int set_all_odd_bits() {
    int odd_bits = 0;
    /*@
      loop invariant 0 <= i <= 31;
      // All odd bits less than `i` are set in `odd_bits`.
      // All even bits less than `i` are zero in `odd_bits`.
      // All bits greater than or equal to `i` in `odd_bits` are zero.
      loop invariant \forall integer k; 0 <= k < i ==> (
          ((odd_bits >> k) & 1) == (if k % 2 == 1 then 1 else 0)
      );
      loop invariant \forall integer k; i <= k < 31 ==> ((odd_bits >> k) & 1) == 0;

      assigns odd_bits, i; // The loop modifies these variables.
      loop variant 31 - i; // Rule II.4: Loop variant for termination.
    */
    for (int i = 0; i < 31; i++) { // Iterate through bit positions 0 to 30 for a 32-bit int.
        if (i % 2 == 1) { // If the current bit position is odd.
            // Rule II.5: Ensure `1U << i` does not overflow.
            // `i` goes up to 30, `1U << 30` fits in unsigned int.
            // `odd_bits` is int, so `1U << i` should fit in int before addition.
            // For i=30, 1U << 30 is 2^30, which fits in a signed 32-bit int.
            // The sum `odd_bits | (1U << i)` will also fit.
            odd_bits = odd_bits | (1U << i); // Set the odd bit.
        }
    }
    return odd_bits;
}
