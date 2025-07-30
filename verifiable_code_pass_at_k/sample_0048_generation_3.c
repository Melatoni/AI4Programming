// Task ID: 48
// Generation: 3

int` is typically `2^31 - 1`. We need to construct a mask where all odd bits are set to 1.

A simple way to construct such a mask is to iterate through bit positions and set the odd ones.
For a 32-bit integer, the odd bit positions are 1, 3, 5, ..., 31.

The mask would be `0b10101010101010101010101010101010`.
In hexadecimal, this is `0xAAAAAAAA`.

The function will simply compute `n | mask`.

/*@
    // Rule II.5: Preconditions to prevent overflow.
    // For a 32-bit signed int, the maximum value is 2^31 - 1.
    // The mask 0xAAAAAAAA is 2,863,311,530.
    // The bitwise OR operation will not overflow if n is within int limits.
    // The result will be at most 2^31 - 1 if n is non-negative and within int limits.
    // If n is negative, the result might still be negative, but within int limits.
    // The problem statement implies positive integers ("given number"), but let's be robust.
    // Assuming n is a standard int, it's already within [INT_MIN, INT_MAX].
    // The bitwise OR operation itself does not cause overflow in the sense of exceeding
    // the representable range, as it operates bit by bit.
    // The result will simply be another int.
    // So, no specific requires related to overflow for the OR operation itself are strictly needed
    // beyond the default assumption that n is a valid int.
    // However, if we were dealing with extremely large numbers or specific bit widths,
    // we would need to consider the type's maximum value.

    assigns \nothing;

    // Rule II.3: Ensures clause for the function's post-condition.
    // The result should have all odd bits set to 1 and even bits set to n's original even bits.
    // Let's define "odd bit" as bit at position k where k % 2 == 1.
    // And "even bit" as bit at position k where k % 2 == 0.
    // For a 32-bit integer, positions are 0 to 31.
    // Odd positions: 1, 3, 5, ..., 31.
    // Even positions: 0, 2, 4, ..., 30.

    // A mask with all odd bits set: 0xAAAAAAAA (binary 1010...1010)
    // For any bit position `k`:
    // If `k` is odd, `\result`'s `k`-th bit must be 1.
    // If `k` is even, `\result`'s `k`-th bit must be the same as `n`'s `k`-th bit.

    // Let's express this using bitwise operations.
    // (\result & (1 << k)) != 0  means k-th bit of \result is 1.
    // (\result & (1 << k)) == 0  means k-th bit of \result is 0.

    // For odd bits: (\result & (1 << k)) != 0 for k = 1, 3, ..., 31
    // This is equivalent to: (\result & 0xAAAAAAAA) == 0xAAAAAAAA
    // For even bits: (\result & (1 << k)) == (n & (1 << k)) for k = 0, 2, ..., 30
    // This is equivalent to: (\result & 0x55555555) == (n & 0x55555555)
    // where 0x55555555 is the mask with all even bits set (0101...0101).

    ensures (\result & 0xAAAAAAAA) == 0xAAAAAAAA &&
            (\result & 0x55555555) == (n & 0x55555555);
*/
int set_odd_bits(int n) {
    // The mask for all odd bits (1, 3, ..., 31) set to 1.
    // In binary: 10101010101010101010101010101010
    // In hex: 0xAAAAAAAA
    // Note: This literal is guaranteed to be an int literal in C.
    // If the system uses 64-bit int, this might be implicitly promoted.
    // However, for typical 32-bit int, this is fine.
    // Frama-C's WP handles int literals properly.
    int odd_bits_mask = 0xAAAAAAAA;

    // Set all odd bits of n to 1 using bitwise OR.
    return n | odd_bits_mask;
}
