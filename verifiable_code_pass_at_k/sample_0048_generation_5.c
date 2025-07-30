// Task ID: 48
// Generation: 5

/*@
    // Rule II.1, II.2: Define a recursive logic function to represent odd bits.
    // This axiomatic block defines what we mean by "odd bits set".
    axiomatic OddBits {
        logic integer set_odd_bits(integer n, integer bit_pos);

        // Base case: If bit_pos is negative, no more bits to set.
        axiom set_odd_bits_base:
            \forall integer n; set_odd_bits(n, -1) == n;

        // Recursive case: If bit_pos is odd, set it. Otherwise, keep it.
        axiom set_odd_bits_rec:
            \forall integer n, bit_pos;
                bit_pos >= 0 ==>
                set_odd_bits(n, bit_pos) ==
                    (if (bit_pos % 2 != 0) then
                        set_odd_bits(n | (1 << bit_pos), bit_pos - 1)
                    else
                        set_odd_bits(n, bit_pos - 1));

        // Rule II.2: Helper axiom to show that setting odd bits doesn't affect even bits already 0.
        // This helps the prover understand the final state.
        axiom set_odd_bits_property_even_bits:
            \forall integer n, bit_pos, k;
                bit_pos >= 0 && k % 2 == 0 && k <= bit_pos && \nth_bit(n, k) == 0 ==>
                \nth_bit(set_odd_bits(n, bit_pos), k) == 0;

        // Rule II.2: Helper axiom to show that setting odd bits sets the odd bits.
        axiom set_odd_bits_property_odd_bits:
            \forall integer n, bit_pos, k;
                bit_pos >= 0 && k % 2 != 0 && k <= bit_pos ==>
                \nth_bit(set_odd_bits(n, bit_pos), k) == 1;

        // Rule II.2: Helper axiom to show that setting odd bits doesn't clear already set bits.
        axiom set_odd_bits_property_unchanged_bits:
            \forall integer n, bit_pos, k;
                bit_pos >= 0 && k <= bit_pos && \nth_bit(n, k) == 1 ==>
                \nth_bit(set_odd_bits(n, bit_pos), k) == 1;
    }
*/

/*@
    requires \valid_read(&n);
    // Rule II.5: Ensure n is non-negative to simplify bitwise operations.
    // Negative numbers have implementation-defined bit representations (two's complement is common but not guaranteed by C standard).
    // For simplicity and verifiability, we constrain to non-negative.
    requires n >= 0;
    // Rule II.5: Prevent overflow for 1 << i. For 32-bit int, 1 << 31 is INT_MIN, 1 << 30 is fine.
    // The loop iterates up to 30 for 31 bits (0 to 30).
    // For 32-bit signed int, the maximum bit position is 30 for positive numbers.
    // We assume a 32-bit integer for 'int'.
    requires n <= 2147483647; // INT_MAX for 32-bit signed int.

    assigns \nothing;

    // Rule II.3: The ensures clause uses logical equivalence.
    // The result should be 'n' with all odd bits up to 30 set.
    ensures \result == set_odd_bits(n, 30);
*/
int set_all_odd_bits(int n) {
    int result = n; // Initialize result with the input number.

    /*@
        loop invariant 0 <= i <= 31;
        // Invariant: All bits from 'i' up to 30 are already processed according to `set_odd_bits`.
        // Equivalently, all odd bits from 'i' up to 30 are set in 'result'.
        loop invariant result == set_odd_bits(n, 30) | (~((1 << i) - 1) & n);
        // Alternative invariant: all odd bits from 'i' up to 30 are set.
        // This is harder to prove with the axiomatic definition.
        // Let's use a more direct property:
        loop invariant \forall integer k; i <= k <= 30 && k % 2 != 0 ==> \nth_bit(result, k) == 1;
        // And that even bits from i to 30 are unchanged
        loop invariant \forall integer k; i <= k <= 30 && k % 2 == 0 ==> \nth_bit(result, k) == \nth_bit(n, k);
        // And that bits lower than i are unchanged.
        loop invariant \forall integer k; 0 <= k < i ==> \nth_bit(result, k) == \nth_bit(n, k);


        loop assigns result, i;
        loop variant 31 - i; // Rule II.4: Loop variant for termination.
    */
    for (int i = 0; i < 31; i++) { // Iterate through bit positions 0 to 30 for a 32-bit integer.
        // Rule I.2: Represent boolean logic using int.
        if (i % 2 != 0) { // Check if the current bit position is odd.
            // Set the odd bit using bitwise OR.
            // Rule II.5: The 'requires' for n <= 2147483647 combined with i < 31 ensures 1 << i does not overflow.
            // For 32-bit signed int, 1 << 30 is the largest positive power of 2. 1 << 31 would be INT_MIN.
            result = result | (1 << i);
        }
    }
    return result;
}
