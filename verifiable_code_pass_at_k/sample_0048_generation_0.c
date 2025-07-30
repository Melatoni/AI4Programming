// Task ID: 48
// Generation: 0

/*@
  requires n >= 0; // The problem implies non-negative numbers.
  requires n <= 2147483647; // Max value for a signed 32-bit integer.
  
  assigns \nothing;

  // Rule II.2: Define a recursive logic function for the property of odd bits.
  // This function returns 1 if the bit at position 'pos' is odd, 0 otherwise.
  // We define it for a specific number 'num' and a maximum bit 'max_bit'.
  axiomatic OddBits {
    logic integer set_odd_bits_recursive(integer num, integer pos, integer max_bit);

    // Base case: If we are beyond the maximum bit, no more bits to set.
    axiom set_odd_bits_recursive_base:
      \forall integer num, max_bit;
        set_odd_bits_recursive(num, max_bit + 1, max_bit) == num;

    // Recursive step: If the position is odd, set the bit using bitwise OR.
    // Otherwise, keep the bit as is.
    axiom set_odd_bits_recursive_step:
      \forall integer num, pos, max_bit;
        0 <= pos <= max_bit ==>
        set_odd_bits_recursive(num, pos, max_bit) ==
        (if pos % 2 != 0 then set_odd_bits_recursive(num | (1 << pos), pos + 1, max_bit)
         else set_odd_bits_recursive(num, pos + 1, max_bit));

    // Rule II.2, II.2.1: Helper axiom for the maximum bit position.
    // This helps the prover understand the maximum bit for a given number.
    logic integer max_bit_pos(integer num);
    axiom max_bit_pos_def:
      \forall integer num;
        max_bit_pos(num) == (if num == 0 then -1 else (integer)(\log_2(num)));

    // Helper axiom: if a bit is set, it remains set in subsequent recursive calls.
    axiom set_odd_bits_recursive_bit_stays_set:
      \forall integer num, pos, max_bit, bit_pos;
        0 <= pos <= max_bit && 0 <= bit_pos <= max_bit && (num >> bit_pos) % 2 == 1 ==>
        (set_odd_bits_recursive(num, pos, max_bit) >> bit_pos) % 2 == 1;

    // Helper axiom: if a bit is at an odd position, it will be set.
    axiom set_odd_bits_recursive_odd_bit_is_set:
      \forall integer num, pos, max_bit, bit_pos;
        0 <= pos <= max_bit && 0 <= bit_pos <= max_bit && bit_pos % 2 != 0 ==>
        (set_odd_bits_recursive(num, pos, max_bit) >> bit_pos) % 2 == 1;

    // Helper axiom: if a bit is at an even position, it remains as it was in the original number.
    axiom set_odd_bits_recursive_even_bit_is_original:
      \forall integer num, pos, max_bit, bit_pos;
        0 <= pos <= max_bit && 0 <= bit_pos <= max_bit && bit_pos % 2 == 0 ==>
        (set_odd_bits_recursive(num, pos, max_bit) >> bit_pos) % 2 == ((num >> bit_pos) % 2);
  }

  // Rule II.3: Ensures clause using logical equivalence.
  // The result should be equal to the number with all odd bits set,
  // up to the maximum bit position relevant for a 32-bit integer (30, as 31 is sign bit).
  ensures \result == set_odd_bits_recursive(n, 0, 30); // For 32-bit signed int, max bit is 30 for positive values.
*/
int set_all_odd_bits(int n) {
    int result = n;
    /*@
      loop invariant 0 <= i <= 31; // i iterates through bit positions 0 to 30.
      // All bits from 0 to i-1 have been processed according to the logic.
      loop invariant result == set_odd_bits_recursive(n, 0, i - 1);
      
      // Each odd bit up to i-1 is set in result.
      loop invariant \forall integer k; 0 <= k < i && k % 2 != 0 ==> (result >> k) % 2 == 1;
      // Each even bit up to i-1 is preserved in result.
      loop invariant \forall integer k; 0 <= k < i && k % 2 == 0 ==> (result >> k) % 2 == ((n >> k) % 2);

      loop assigns result, i;
      loop variant 31 - i; // Loop variant for termination.
    */
    for (int i = 0; i < 31; i++) { // Iterate up to bit 30 for a 32-bit signed integer.
        if (i % 2 != 0) {
            // Set the i-th bit using bitwise OR.
            // Rule II.5: Prevent overflow with `1 << i`.
            // Max i is 30, so 1 << 30 is fine.
            result = result | (1 << i);
        }
    }
    return result;
}
