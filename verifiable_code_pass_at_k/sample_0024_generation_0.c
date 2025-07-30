// Task ID: 24
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  axiomatic BinToDec {
    logic integer bin_to_dec_rec(int *arr, int start, int end);

    axiom bin_to_dec_rec_base:
      \forall int *arr, int start;
        bin_to_dec_rec(arr, start, start) == arr[start];

    axiom bin_to_dec_rec_recursive:
      \forall int *arr, int start, int end;
        start < end ==> bin_to_dec_rec(arr, start, end) == bin_to_dec_rec(arr, start, end - 1) * 2 + arr[end];

    // Helper axiom: if all bits are 0 or 1, the result is non-negative.
    axiom bin_to_dec_rec_non_negative:
      \forall int *arr, int start, int end;
        (\forall integer k; start <= k <= end ==> (arr[k] == 0 || arr[k] == 1)) ==> bin_to_dec_rec(arr, start, end) >= 0;

    // Helper axiom: upper bound for the result. Max value is 2^len - 1.
    // For a 31-bit number (max for positive int), 2^31 - 1 = 2147483647
    // This axiom helps prove that if the input length is not too large, the result fits in int.
    axiom bin_to_dec_rec_upper_bound:
      \forall int *arr, int start, int end;
        (\forall integer k; start <= k <= end ==> (arr[k] == 0 || arr[k] == 1)) ==>
        bin_to_dec_rec(arr, start, end) <= (1 << (end - start + 1)) - 1;
  }
*/

/*@
  requires n > 0;
  // Rule II.5: Prevent overflow. Max length for a 31-bit positive integer is 31.
  // A 31-bit binary number can be represented by `int`.
  // If n is 31, 1 << n would overflow. So n must be at most 30 to allow 1 << (n-1) to be computed.
  // Or, more precisely, ensure the final result fits in int.
  // Max positive int is 2^31 - 1.
  // So, 2^n - 1 <= 2^31 - 1 => n <= 31.
  // We need to ensure that 2^(n-1) (the highest power of 2) doesn't overflow intermediate calculations.
  // For `int`, 2^30 is the largest power of 2 that doesn't overflow. So n should be at most 31.
  // We constrain n to prevent potential overflow of intermediate `power_of_2` values or final sum.
  // The largest value 2^30 is 1073741824.
  // If n = 31, the highest power is 2^30.
  // So, n <= 31 is sufficient to ensure result fits in `int`.
  requires n <= 31; // Max length for result to fit in a signed int.

  // Rule I.3: Array parameter `binary_array` decays to a pointer.
  requires \valid_read(binary_array + (0..n-1));
  // All elements must be 0 or 1.
  requires \forall integer i; 0 <= i < n ==> (binary_array[i] == 0 || binary_array[i] == 1);

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like functions.
  // Here, it returns an integer, so direct equality is fine.
  ensures \result == bin_to_dec_rec(binary_array, 0, n - 1);
  ensures \result >= 0;
*/
int binaryToDecimal(int *binary_array, int n) {
    int decimal_value = 0;
    int power_of_2 = 1;

    /*@
      loop invariant 0 <= i <= n;
      // The decimal value accumulated so far corresponds to the processed bits.
      // The processed bits are from index n-1 down to n-i.
      loop invariant decimal_value == bin_to_dec_rec(binary_array, n - i, n - 1);
      // The current power_of_2 corresponds to 2^(i).
      // Rule II.5: Ensure power_of_2 does not overflow.
      // power_of_2 is 2^i. Max i is n. So 2^n.
      // If n is 31, 2^31 would overflow.
      // If n is 30, 2^30 is fine.
      // The loop condition `i < n` means that `i` goes from 0 to `n-1`.
      // So `power_of_2` will be 2^0, 2^1, ..., 2^(n-1).
      // If n=31, `i` goes up to 30. `power_of_2` goes up to 2^30, which is fine.
      loop invariant power_of_2 == (1 << i);
      loop assigns decimal_value, power_of_2, i;
      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // Rule II.5: Prevent overflow for addition.
        // Check if decimal_value + binary_array[n - 1 - i] * power_of_2 will overflow.
        // The max value for decimal_value is 2^31 - 1.
        // The max value for power_of_2 is 2^30.
        // binary_array[n - 1 - i] is 0 or 1.
        // If binary_array[n - 1 - i] is 1, then decimal_value + power_of_2.
        // This is implicitly handled by the `n <= 31` requires clause on the function.
        // Frama-C/WP will use that to prove this addition does not overflow.
        decimal_value = decimal_value + binary_array[n - 1 - i] * power_of_2;

        // Rule II.5: Prevent overflow for multiplication (power_of_2 * 2).
        // This multiplication happens only if i < n-1.
        // If n=31, max i is 30. Last power_of_2 is 2^30.
        // If i = 30, power_of_2 * 2 would be 2^31, which overflows if `power_of_2` is `int`.
        // This implies that `power_of_2` cannot reach 2^30 if `n` is 31.
        // The loop condition `i < n` means that `power_of_2` is `1 << i`.
        // The last iteration is when `i = n-1`.
        // In this last iteration, `power_of_2` is `1 << (n-1)`.
        // After the addition, `power_of_2` becomes `1 << n`.
        // If `n=31`, `power_of_2` becomes `1 << 31`, which is an overflow for signed int.
        // To prevent this, the `power_of_2 = power_of_2 * 2;` line should be conditional or handled.
        // However, the `power_of_2` value is only used in the next iteration.
        // If it's the last iteration, the value is not used.
        // A common pattern is to update the power before the addition.
        // Let's adjust the loop to prevent this overflow.
        // If `i` is `n-1`, `power_of_2` is `1 << (n-1)`. This is the largest used power.
        // The next update `power_of_2 * 2` should not happen if `i == n-1`.

        // Let's adjust the loop to compute power_of_2 first.
        // This requires changing the loop invariant slightly.
        // A simpler way is to note that this update is only relevant for the next iteration.
        // If `i == n-1`, this `power_of_2 * 2` is not used.
        // Frama-C might still complain about the potential overflow on the last iteration.
        // A common solution is to move the update to the beginning of the loop or make it conditional.
        // Let's keep it here and rely on `n <= 31`.
        // If n=31, max i is 30.
        // When i=30, power_of_2 = 1 << 30.
        // Then power_of_2 * 2 = 1 << 31, which is INT_MIN if int is 32-bit.
        // This is an overflow. The `n <= 31` constraint is not enough to prevent this specific overflow.
        // Max `n` must be 30 for `power_of_2` not to overflow if we multiply it by 2.
        // If `n` is 31, `power_of_2` can be `1 << 30`.
        // The `power_of_2 = power_of_2 * 2` would then overflow.
        // The `requires n <= 30` would be safer if `power_of_2` is updated unconditionally.
        // Let's assume `n <= 30` for this specific pattern to pass, or add a condition.
        // Adding a condition: `if (i < n - 1) power_of_2 = power_of_2 * 2;`
        // Given the problem statement requires *verifiable*, let's ensure it.

        if (i < n - 1) { // Rule III.1: No C-style ternary in ACSL. This is C code.
            // Rule II.5: Ensure power_of_2 * 2 does not overflow.
            // This is guaranteed by n <= 30. If n=30, max i is 29.
            // So max power_of_2 is 1 << 29. Then power_of_2 * 2 is 1 << 30, which fits in int.
            power_of_2 = power_of_2 * 2;
        }
    }
    return decimal_value;
}
