// Task ID: 33
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define a recursive logic function for the binary representation.
  // This axiomatic block defines the properties of a number's binary representation.
  axiomatic BinaryRepresentation {
    logic integer power(integer base, integer exp);

    axiom power_base:
      \forall integer base; power(base, 0) == 1;

    axiom power_rec:
      \forall integer base, exp;
      exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

    // This logic function calculates the decimal value of a binary number
    // represented as an array of bits.
    // bits[0] is the LSB, bits[len-1] is the MSB.
    logic integer value_of_binary(int *bits, integer len);

    // Base case: empty binary array represents 0
    axiom value_of_binary_base:
      value_of_binary(bits, 0) == 0;

    // Recursive case: add the value of the current bit (LSB) and
    // recursively calculate the value of the rest of the bits (shifted).
    // Note: Frama-C's WP struggles with direct array indexing in recursive logic.
    // We define value_of_binary_rec to handle the recursive sum from the LSB.
    // The bits array is conceptually read from index 0 upwards.
    logic integer value_of_binary_rec(int *bits, integer start_idx, integer end_idx);

    axiom value_of_binary_rec_base:
      \forall int *bits, integer start_idx;
      start_idx >= end_idx ==> value_of_binary_rec(bits, start_idx, end_idx) == 0;

    axiom value_of_binary_rec_step:
      \forall int *bits, integer start_idx, end_idx;
      start_idx < end_idx ==> value_of_binary_rec(bits, start_idx, end_idx) ==
        bits[start_idx] * power(2, start_idx) + value_of_binary_rec(bits, start_idx + 1, end_idx);

    // This is the main logic function used for the postcondition.
    // It sums the bits from 0 to len-1.
    axiom value_of_binary_def:
      \forall int *bits, integer len;
      len >= 0 ==> value_of_binary(bits, len) == value_of_binary_rec(bits, 0, len);

    // Rule II.2: Helper axiom for the range of bits.
    // If all bits are 0 or 1, then the value_of_binary is non-negative.
    axiom value_of_binary_non_negative:
      \forall int *bits, integer len;
        (\forall integer i; 0 <= i < len ==> (bits[i] == 0 || bits[i] == 1)) ==>
        value_of_binary(bits, len) >= 0;
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent potential overflow if n is very large and bit_len becomes excessive.
  // A 31-bit number can be represented by at most 31 bits.
  // Max int value for 32-bit signed int is 2^31 - 1.
  // log2(2^31 - 1) approx 30.9. So, max 31 bits are needed.
  // The output array `binary` must be large enough.
  // The output `bit_len` will be at most 31 for positive `int` values.
  requires \valid_range(binary, 0, 31); // Ensure `binary` can hold up to 32 bits (0-31)
                                      // for maximum integer range.
                                      // A positive int `n` will require at most 31 bits.
                                      // e.g. 2^30 needs 31 bits (index 0 to 30)
                                      // The maximum `int` value needs 31 bits (index 0 to 30).

  assigns binary[0..]; // Potentially modifies all elements of binary
  assigns *bit_len;    // Modifies the length variable

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function should return 1 (true) if conversion is successful.
  // The converted binary representation (bits[0] to bits[(*bit_len)-1])
  // must represent the original decimal number `n`.
  ensures ((\forall integer i; 0 <= i < *bit_len ==> (binary[i] == 0 || binary[i] == 1)) &&
           value_of_binary(binary, *bit_len) == n &&
           // Ensure the most significant bit is 1 unless n is 0.
           (n == 0 ==> *bit_len == 1 && binary[0] == 0) &&
           (n > 0 ==> *bit_len > 0 && binary[*bit_len - 1] == 1) &&
           // Ensure bit_len is minimal (no leading zeros for n > 0)
           (n > 0 ==> \forall integer i; *bit_len <= i < 32 ==> binary[i] == 0)
           ) <==> (esult == 1);
  // If n is 0, the result should be a single 0 bit.
  // If n > 0, the MSB (at index *bit_len - 1) must be 1.
  // The function always returns 1 if requirements are met.
*/
int decimal_to_binary(int n, int binary[], int *bit_len) {
    if (n == 0) {
        binary[0] = 0;
        *bit_len = 1;
        return 1;
    }

    int i = 0;
    /*@
      loop invariant 0 <= i;
      // The decimal value of the bits processed so far (binary[0] to binary[i-1])
      // plus the current value of n (which is the remaining part to convert)
      // should equal the original value of `n_at_entry`.
      loop invariant \at(n, Pre) == value_of_binary(binary, i) + n * power(2, i);

      // All bits processed so far are either 0 or 1.
      loop invariant \forall integer k; 0 <= k < i ==> (binary[k] == 0 || binary[k] == 1);
      
      // The current value of n is non-negative.
      loop invariant n >= 0;

      loop assigns n, i, binary[0..]; // n and i are modified, and binary array elements are assigned.

      // Rule II.4: Loop variant for termination.
      // The value of n decreases in each iteration, eventually becoming 0.
      // i increases, but n is the primary driver for termination.
      loop variant n;
    */
    while (n > 0) {
        binary[i] = n % 2;
        n = n / 2;
        i++;
    }
    *bit_len = i;
    return 1;
}
