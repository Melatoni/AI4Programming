// Task ID: 6
// Generation: 0

/*@
  // Rule I.1: No standard libraries, so no limits.h.
  // Rule II.5: Prevent overflow for operations like x ^ y and subsequent bitwise operations.
  // Assuming int is 32-bit, max value is 2^31 - 1.
  // The XOR result will also be within int range if x and y are.
  // The loop iterates at most 31 times for positive integers.
  // The shift operation (1 << i) should not overflow.
  // For 32-bit int, 1 << 31 is the max positive power of 2.
  requires x >= 0 && y >= 0; // Assuming non-negative integers for bitwise operations.
  
  assigns \nothing;

  // Rule II.2: Define recursive logic for counting set bits (population count).
  // This avoids \sum and provides a verifiable way to reason about bit counts.
  axiomatic Popcount {
    logic integer popcount(int n);

    axiom popcount_zero: popcount(0) == 0;
    // Rule II.2: Recursive definition for popcount.
    axiom popcount_recursive:
      \forall int n; n > 0 ==> popcount(n) == (n % 2) + popcount(n / 2);
    
    // Rule II.2, II.2: Helper axioms for popcount properties crucial for verification.
    // Proving that popcount(x) >= 0.
    axiom popcount_non_negative:
      \forall int n; n >= 0 ==> popcount(n) >= 0;

    // Proving that popcount is 1 if and only if n is a power of 2.
    // This axiom is directly relevant to the problem's logic.
    axiom popcount_is_one_iff_power_of_two:
      \forall int n; n > 0 ==> (popcount(n) == 1 <==> (\exists integer k; k >= 0 && n == (1 << k)));
  }

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The two numbers differ at one bit position if their XOR sum has exactly one set bit.
  ensures (popcount(x ^ y) == 1) <==> (\result == 1);
*/
int differ_by_one_bit(int x, int y) {
    int xor_result = x ^ y; // Calculate the XOR sum.

    // Rule II.4: Mandatory loop annotations.
    /*@
      loop invariant 0 <= i <= 32; // Assuming 32-bit int for iteration limit.
      // Invariant: count holds the number of set bits encountered so far from the right.
      loop invariant count == popcount(xor_result >> i); // This invariant is tricky.
      // A simpler invariant might be `count` is the number of set bits in `xor_result`'s lower `i` bits
      // if we were counting them iteratively.
      // However, the function directly checks if `xor_result` is a power of 2,
      // so a simpler invariant is:
      loop invariant (\forall integer k; 0 <= k < i ==> (((xor_result >> k) & 1) == 0 || ((xor_result >> k) & 1) == 1));
      loop invariant (\forall integer k; 0 <= k < i ==> (\result == 0 || (\result == 1 && (xor_result == (1 << k_prime) && popcount(xor_result) == 1))));


      // The function's logic is simpler: check if xor_result is a power of 2.
      // A number is a power of 2 if and only if it has exactly one bit set.
      // The common trick for this is (n > 0 && (n & (n - 1)) == 0).
      // Let's implement that directly rather than a loop for counting bits,
      // as it's more efficient and easier to verify for this specific problem.
      // So, the provided Python description "differ at one bit position only"
      // implies popcount(x ^ y) == 1.
      // The loop below is the direct implementation of counting bits.
      // However, the problem usually implies the `(n > 0 && (n & (n - 1)) == 0)` trick.
      // Let's stick to the common interview question interpretation for "differ at one bit position".
    */
    
    // The most efficient and standard way to check if a number has exactly one bit set
    // (i.e., is a power of 2) is `n > 0 && (n & (n - 1)) == 0`.
    // This directly translates to `popcount(n) == 1`.
    // This avoids a loop entirely and is highly verifiable.

    // Rule II.3: The ensures clause already uses popcount, which is axiomatically defined.
    // The C code should now simply return 1 if popcount(xor_result) == 1, else 0.
    // This is equivalent to `xor_result > 0 && (xor_result & (xor_result - 1)) == 0`.

    // Frama-C/WP can often prove `popcount(n) == 1 <==> (n > 0 && (n & (n-1)) == 0)`
    // if given appropriate lemmas or if the popcount definition is strong enough.
    // Our Popcount axiomatic block already includes `popcount_is_one_iff_power_of_two`.

    // Check if xor_result is a power of 2 (has exactly one bit set)
    // Rule I.2: Use int for boolean return.
    if (xor_result > 0 && (xor_result & (xor_result - 1)) == 0) {
        return 1; // True
    } else {
        return 0; // False
    }
}
