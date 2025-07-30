// Task ID: 48
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: int for booleans.
  // Rule I.3: Array pointer decay (not applicable here).

  // Rule II.5: Prevent runtime errors.
  // For a 32-bit integer, setting all odd bits might exceed INT_MAX if n is large.
  // The maximum possible value for a 32-bit unsigned int (all bits set) is 0xFFFFFFFF.
  // This function modifies bits, it doesn't just read them.
  // The result will be n | 0xAAAAAAAA (for 32-bit).
  // We need to ensure that n, after ORing with 0xAAAAAAAA, does not overflow
  // a signed int.
  // The maximum value for a signed int is INT_MAX (typically 2^31 - 1).
  // If n is positive, n | 0xAAAAAAAA must be <= INT_MAX.
  // If n is negative, it's more complex, but typically we assume non-negative inputs
  // for bit manipulation unless otherwise specified. Let's assume n >= 0.
  // The largest odd-bit mask for 32-bit is 0xAAAAAAAA.
  // If n has any bit set at an even position such that n | 0xAAAAAAAA > INT_MAX,
  // then overflow occurs.
  // For example, if n = 0x55555555, then n | 0xAAAAAAAA = 0xFFFFFFFF, which is -1
  // for signed int, an overflow if interpreted as positive.
  // A safe upper bound for n would be INT_MAX - 0xAAAAAAAA.
  // Or, more simply, require that the most significant bit (bit 31) is 0 in n,
  // and bit 31 in 0xAAAAAAAA is 1. If n has MSB 0, and we OR it with 0xAAAAAAAA,
  // the MSB will become 1, which might lead to a negative number if interpreted
  // as signed.
  // Let's assume the intent is for unsigned interpretation, or that the result
  // fits into a signed int.
  // Given that the problem is "set all odd bits", it implies bitwise operations.
  // For simplicity and verifiability, let's constrain `n` such that `n` is non-negative
  // and the result will still be positive and fit within `int`.
  // The largest mask for 32-bit odd bits is 0xAAAAAAAA.
  // If `n` has bit 31 set, and bit 31 of 0xAAAAAAAA is 1, the result will be negative.
  // We should require `n` to be within a range that ensures the result is positive
  // and fits `int`.
  // The highest bit that is an odd position in a 32-bit integer is bit 31.
  // No, the highest *odd-indexed* bit is bit 31.
  // Bit 0 (even), Bit 1 (odd), Bit 2 (even), Bit 3 (odd)... Bit 30 (even), Bit 31 (odd).
  // So, 0xAAAAAAAA has bit 31 set.
  // If n has bit 31 set, then n is negative.
  // If n has bit 30 set, and bit 31 is 0, and we OR with 0xAAAAAAAA, bit 31 becomes 1.
  // This transforms a positive number (up to 2^30 - 1) into a negative number.
  // To ensure the result is non-negative and fits `int`, we must constrain `n`
  // such that `n | 0xAAAAAAAA` does not make the sign bit 1.
  // This means that if `n` itself is positive, `n | 0xAAAAAAAA` should not exceed `INT_MAX`.
  // Since 0xAAAAAAAA has bit 31 set, then `n | 0xAAAAAAAA` will have bit 31 set.
  // This is problematic for signed `int`.
  //
  // Let's assume the problem implies an unsigned interpretation of the number,
  // or that it's okay for the result to be negative if the most significant odd bit is set.
  // Frama-C's WP typically works with signed `int` unless `unsigned int` is used.
  // If we assume `n` is a non-negative integer, and the result should also be
  // interpretable as a non-negative integer, then `n` must be small enough.
  // `INT_MAX` is typically `2^31 - 1`.
  // The odd bit mask for 32-bit is `0xAAAAAAAA`.
  // So, `n | 0xAAAAAAAA` must be `<= INT_MAX`.
  // This implies that `n` can only have bits set up to bit 30, and bit 30 must be 0
  // if bit 31 of 0xAAAAAAAA is 1.
  // This is a strong constraint.
  // A more practical approach for "set all odd bits" is to acknowledge that
  // the result might become negative if the most significant odd bit (bit 31) is set.
  //
  // Let's reformulate the `requires` to prevent overflow of `int` type.
  // If `n` is non-negative and `n | 0xAAAAAAAA` would make it negative, that's overflow.
  // So, if `n >= 0`, we must have `(n | 0xAAAAAAAA) >= 0`.
  // This implies that the most significant bit (bit 31) of `n | 0xAAAAAAAA` must be 0.
  // But `0xAAAAAAAA` has bit 31 set. So this constraint is impossible for a 32-bit `int`.
  //
  // This suggests we might need to use `unsigned int`.
  // Let's stick to `int` as per Rule I.2 and assume the typical use case for bitwise ops
  // where the result is interpreted as a bit pattern, not necessarily a positive value.
  // The only runtime error that can happen is if `n` itself is problematic,
  // or if the operation on `n` leads to an unrepresentable value.
  // Bitwise OR (`|`) does not cause overflow for `int` types in C.
  // The standard guarantees that bitwise operations on `int` types produce
  // values of type `int`. If the result of `|` operation exceeds `INT_MAX`
  // for positive numbers or goes below `INT_MIN` for negative numbers,
  // the behavior is implementation-defined.
  // Frama-C's default behavior for `int` is typically to assume two's complement.
  // In two's complement, `0xAAAAAAAA` is a negative number.
  // Let's define the mask for 32-bit integers.
  // The mask should be `0b10101010101010101010101010101010`.
  // This is `0xAAAAAAAA`.
  // We need to ensure that the result `n | 0xAAAAAAAA` is within `INT_MIN` and `INT_MAX`.
  // This is inherent to the bitwise OR operation for `int` in C.
  // The result of `a | b` is always representable as an `int` if `a` and `b` are `int`.
  // So no `requires` for overflow for the `|` operation itself.
  // The only `requires` would be for the input `n` to be within `int` range,
  // which is implicitly handled by the type `int`.

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions (not applicable for this function,
  // which returns a modified number, not a boolean).

  // Define a logic function to represent the odd bits mask.
  // This needs to be axiomatic if it's dynamic based on bit width.
  // For a fixed 32-bit int, we can use a constant.
  // Let's define it generally for different bit widths if needed, but for 'int',
  // we assume 32-bit as common.
  //
  // Axiomatic block for recursive logic (Rule II.1)
  // For this problem, a simple constant mask is sufficient.
  // However, if we were to define "all odd bits" for a generic bit length `L`,
  // we would use a recursive logic function.
  // Example for a generic `L`:
  // axiomatic OddBitsMask {
  //   logic integer odd_mask(integer L);
  //   axiom odd_mask_base: odd_mask(0) == 0;
  //   axiom odd_mask_rec_even: \forall integer L; L > 0 && L % 2 == 0 ==> odd_mask(L) == (odd_mask(L-1) << 1);
  //   axiom odd_mask_rec_odd: \forall integer L; L > 0 && L % 2 == 1 ==> odd_mask(L) == ((odd_mask(L-1) << 1) | 1);
  // }
  // Then the ensures clause would use `odd_mask(32)`.
  // For this problem, let's directly use the 32-bit constant.

  // The ensures clause: The result should be `n` with all odd-indexed bits set to 1.
  // This means `result` should be `n | MASK`, where MASK has 1s at odd positions
  // and 0s at even positions.
  // For a 32-bit integer, the odd bits are 1, 3, 5, ..., 31.
  // The mask is `...10101010` in binary.
  // This is `0xAAAAAAAA`.

  ensures \result == (n | 0xAAAAAAAA);
*/
int set_all_odd_bits(int n) {
    // The mask for all odd bits (1, 3, 5, ..., 31 for a 32-bit int).
    // In binary: 10101010101010101010101010101010
    // In hexadecimal: 0xAAAAAAAA
    int odd_bits_mask = 0xAAAAAAAA; // Rule I.1: No limits.h, so no INT_MAX/MIN.

    // Rule II.4: No loops, so no loop annotations needed.

    // Rule III.1: No C-style ternary in ACSL. (Not applicable here as no ACSL ternary needed)
    // Rule III.2: No parentheses around if-then-else. (Not applicable)
    // Rule III.3: Correct range syntax. (Not applicable)
    // Rule III.4: No stray semicolons. (Not applicable)

    return n | odd_bits_mask;
}
