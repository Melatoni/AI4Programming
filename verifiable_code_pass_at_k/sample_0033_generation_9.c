// Task ID: 33
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay not applicable here.

  // Rule II.5: Prevent runtime errors.
  // The maximum value for an int is INT_MAX (typically 2^31 - 1).
  // Each bit can be 0 or 1. A 32-bit integer needs at most 32 bits for its binary representation.
  // The array `binary` must be large enough to hold all bits.
  // For positive numbers, the maximum number of bits is 31 (for 2^31 - 1).
  // For 0, it's 1 bit ("0").
  // So, a size of 32 (or more) is sufficient.
  requires n >= 0;
  requires max_bits > 0; // The array size must be positive.
  requires max_bits >= 32; // Ensure enough space for a 31-bit integer plus sign, or 0.

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like return.
  // The function returns the number of bits in the binary representation.
  // This is a boolean-like function in the sense that its *success* is tied to
  // the 'binary' array being correctly filled up to the returned count.
  // We specify what 'result' means in terms of the output array.
  // The result `k` means that `binary[0..k-1]` contains the binary representation,
  // and `binary[k]` onwards are undefined (or 0 if initialized).
  //
  // Let's define what a correct binary conversion means.
  // It means that `n` can be reconstructed from the bits in `binary` array.
  // The `result` is the number of bits used.
  //
  // Rule II.2: Recursive logic for complexity.
  // Define a logic function to compute the value of a binary array.
  axiomatic BinaryConversion {
    logic integer sum_power_of_2(int* arr, integer high, integer low);

    axiom sum_power_of_2_base:
      \for_all int* arr, integer high;
        sum_power_of_2(arr, high, high) == 0; // Empty range sums to 0.

    axiom sum_power_of_2_recursive:
      \for_all int* arr, integer high, integer low;
        low < high ==> sum_power_of_2(arr, high, low) == arr[low] * \pow(2, low) + sum_power_of_2(arr, high, low + 1);

    // Helper axiom: If all bits are 0 or 1, then the sum is non-negative.
    // This is implicitly handled by the definition, but good to think about.
    // We also need to state that the bits are indeed 0 or 1.
    // This will be part of the loop invariant.
  }

  // The ensures clause describes the post-condition.
  // If n is 0, the result is 1 and binary[0] is 0.
  // If n > 0, the result `k` is the number of bits, and the sum of powers of 2
  // from `binary[0]` to `binary[k-1]` must equal `n`.
  // Also, each bit in `binary[0..k-1]` must be 0 or 1.
  ensures (n == 0 ==> \result == 1 && binary[0] == 0) &&
          (n > 0 ==> \result > 0 && \result <= max_bits &&
                       sum_power_of_2(binary, \result, 0) == n &&
                       (\forall integer i; 0 <= i < \result ==> (binary[i] == 0 || binary[i] == 1)));

  assigns binary[0..max_bits-1];
*/
int decimal_to_binary(int n, int binary[], int max_bits) {
    if (n == 0) {
        binary[0] = 0;
        return 1;
    }

    int i = 0;
    /*@
      loop invariant 0 <= i <= max_bits;
      // The current value of 'n' (after divisions) plus the sum of the bits
      // already extracted (binary[0] to binary[i-1]) should equal the original 'n'.
      // This is the core invariant relating the loop state to the initial input.
      loop invariant \at(n, Pre) == (\at(n, LoopCurrent) * \pow(2, i) + sum_power_of_2(binary, i, 0));
      // All bits written so far are 0 or 1.
      loop invariant \forall integer k; 0 <= k < i ==> (binary[k] == 0 || binary[k] == 1);
      // Ensure we don't write beyond the array bounds.
      loop invariant i < max_bits || n == 0; // If n becomes 0, i might be equal to max_bits at loop exit.

      loop assigns i, n, binary[0..max_bits-1];
      // Rule II.4: Loop variant for termination.
      // The value of n strictly decreases (when n > 0), or i increases.
      // n is always positive here, so n is a good variant.
      loop variant n;
    */
    while (n > 0 && i < max_bits) {
        binary[i] = n % 2;
        n = n / 2;
        i++;
    }

    // The result is the number of bits used, which is `i`.
    // We need to prove that `i` is indeed the correct number of bits and
    // that the `binary` array correctly represents `n`.
    return i;
}
