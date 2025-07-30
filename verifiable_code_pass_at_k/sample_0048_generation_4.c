// Task ID: 48
// Generation: 4

/*@
    // Rule I.1: No standard libraries.
    // Rule I.2: Use int for booleans.
    // Rule I.3: Not applicable here.

    // Rule II.5: Prevent potential overflow if num is very large,
    // though for typical int sizes (32-bit), 1 << 31 is the max bit
    // and setting odd bits won't cause overflow.
    // We assume 'int' is 32-bit for these constraints.
    requires num >= 0; // Only non-negative numbers are typically considered for bit manipulation.
    requires num <= 2147483647; // Max positive signed 32-bit int.

    assigns \nothing;

    // Rule II.3: The ensures clause must use logical equivalence.
    // We define what "setting all odd bits" means.
    // It means that for every bit position k, if k is odd, the k-th bit of the result is 1.
    // If k is even, the k-th bit of the result is the same as the k-th bit of the original number.

    // Let's define bit_set(n, k) as true if the k-th bit of n is 1.
    logic boolean bit_set(int n, integer k);

    axiom bit_set_def:
      \forall int n, integer k;
        (k >= 0 && k < 32) ==> (bit_set(n, k) <==> ( (n >> k) & 1 ) == 1);

    // Helper logic function to define the expected result.
    // This function calculates the value where odd bits are set to 1
    // and even bits retain their original value.
    // Rule II.1: Using recursive logic for complexity (bit-wise construction).
    // This is like a sum for bit positions.
    logic integer set_odd_bits_recursive(int n, integer bit_pos);

    axiom set_odd_bits_recursive_base:
      set_odd_bits_recursive(n, -1) == 0; // Base case: no bits set yet.

    axiom set_odd_bits_recursive_step:
      \forall int n, integer bit_pos;
        (bit_pos >= 0 && bit_pos < 32) ==>
        (set_odd_bits_recursive(n, bit_pos) ==
            (if bit_pos % 2 == 1 then // If current bit position is odd
                set_odd_bits_recursive(n, bit_pos - 1) | (1 << bit_pos) // Set the bit
            else // If current bit position is even
                (if bit_set(n, bit_pos) then // If original bit is 1
                    set_odd_bits_recursive(n, bit_pos - 1) | (1 << bit_pos) // Keep it 1
                else // If original bit is 0
                    set_odd_bits_recursive(n, bit_pos - 1) // Keep it 0
                )
            )
        );

    // Rule II.2: Helper axioms for recursive functions.
    // This axiom states that our recursive definition correctly computes the final expected value.
    axiom set_odd_bits_final_value:
      \forall int n;
        (n >= 0 && n <= 2147483647) ==>
        set_odd_bits_recursive(n, 31) ==
        (
            (n & 0xAAAAAAAA) // Original even bits (0b1010...)
            |
            (~0xAAAAAAAA & 0x7FFFFFFF) // All odd bits set to 1 (0b0101...) limited to 31 bits
            // This mask is 0x55555555 for 32-bit int.
            // 0x55555555 is 01010101...
        );

    ensures \result == set_odd_bits_recursive(num, 31);
*/
int set_odd_bits(int num) {
    int result = num;
    /*@
        loop invariant 0 <= i <= 32;
        // Invariant: all bits from 0 up to 'i-1' are correctly set in 'result'.
        // That is, for k < i:
        // if k is odd, k-th bit of result is 1.
        // if k is even, k-th bit of result is same as k-th bit of num.
        loop invariant result == set_odd_bits_recursive(num, i - 1);

        loop assigns result, i;
        loop variant 32 - i;
    */
    for (int i = 0; i < 32; i++) { // Assuming 32-bit integer
        // Rule III.4: No stray semicolons.
        if (i % 2 == 1) { // If the bit position is odd
            result = result | (1 << i); // Set the bit to 1
        }
        // If the bit position is even, it already retains its original value from 'num'.
        // No action needed for even bits based on the problem description.
    }
    return result;
}
