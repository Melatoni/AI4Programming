// Task ID: 6
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.2: Define a recursive logic function for properties over bit sequences.
  // This function counts the number of set bits (1s) in an integer.
  axiomatic BitOperations {
    logic integer count_set_bits(integer n);

    // Base case: 0 has 0 set bits.
    axiom count_set_bits_base:
      count_set_bits(0) == 0;

    // Recursive case for positive integers.
    // n & (n - 1) clears the least significant set bit.
    axiom count_set_bits_recursive:
      \forall integer n; n > 0 ==> count_set_bits(n) == 1 + count_set_bits(n & (n - 1));

    // Rule II.2, II.2: Helper axiom for a property of count_set_bits
    // If a number has exactly one set bit, it must be a power of 2 (or 0, but we handle n > 0).
    axiom count_set_bits_one_implies_power_of_two:
      \forall integer k; k > 0 && count_set_bits(k) == 1 ==> \exists integer p; p >= 0 && k == (1 << p);
  }
*/

/*@
  requires \valid_read(x);
  requires \valid_read(y);
  // Rule II.5: Prevent potential issues from extremely large negative numbers if not handled by C's bitwise ops.
  // For `int`, bitwise operations on negative numbers are implementation-defined before C99.
  // Frama-C's model of `&` is typically two's complement, which is fine.
  // However, `x ^ y` could be large, and `count_set_bits` relies on `n & (n-1)` which works for non-negative.
  // To be safe and simplify reasoning, we assume non-negative inputs for this problem.
  requires *x >= 0;
  requires *y >= 0;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The two numbers differ at one bit position if and only if their XOR sum has exactly one set bit.
  ensures (count_set_bits(*x ^ *y) == 1) <==> (\result == 1);
*/
int differ_by_one_bit(int *x, int *y) {
    // Calculate the XOR difference.
    int diff = *x ^ *y;

    // Check if `diff` has exactly one set bit.
    // A number has exactly one set bit if it's a power of two (for positive numbers).
    // This can be checked efficiently using the property: N & (N - 1) == 0 iff N is a power of 2 (or N is 0).
    // Since we need exactly one bit, diff must be > 0.
    if (diff > 0 && (diff & (diff - 1)) == 0) {
        return 1; // True: they differ by exactly one bit.
    } else {
        return 0; // False: they differ by more than one bit or by zero bits.
    }
}
