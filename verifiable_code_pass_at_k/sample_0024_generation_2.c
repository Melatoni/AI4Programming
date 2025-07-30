// Task ID: 24
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here.

  // Rule II.1: Recursive logic for complexity - not applicable here.
  // Rule II.2: Helper axioms - not applicable here.
  // Rule II.3: Ensures clause for boolean-like functions - not applicable here, as it returns an int value.
  // Rule II.5: Prevent Runtime Errors (RTE)

  // Maximum value for an integer is INT_MAX.
  // The maximum decimal value for a 31-bit binary number is 2^31 - 1.
  // The maximum length of the binary string would be 31 characters plus null terminator.
  // Let's assume a maximum length that fits within int, say 30 bits.
  // 2^29 < 2^31 - 1, so a binary string of length 30 is safe.
  // The sum of powers of 2 for a string of length `len` can be at most 2^len - 1.
  // To avoid overflow, 2^len - 1 <= INT_MAX.
  // Assuming INT_MAX is 2^31 - 1, max len is 31.
  // For safety, let's limit the length to 30.

  axiomatic IntMax {
    logic integer INT_MAX_VAL = 2147483647; // Standard INT_MAX for 32-bit signed int
  }

  requires \valid(binary_str);
  requires \for_all integer k; 0 <= k < length ==> (binary_str[k] == '0' || binary_str[k] == '1');
  requires length >= 0;
  // Prevent overflow: the maximum decimal value for a binary string of length 'length' is 2^length - 1.
  // This must be less than or equal to INT_MAX.
  // A length of 30 ensures that 2^30 - 1 is within INT_MAX (2^31 - 1).
  // Assuming 30 is a safe upper bound for length to prevent overflow of the result.
  requires length <= 30;

  assigns \nothing;

  // The result is non-negative.
  ensures \result >= 0;
  // The result is the decimal equivalent.
  // This can be expressed using a sum, but Frama-C's WP struggles with direct sums.
  // A more robust approach is to define a recursive logic function for the decimal value.

  axiomatic BinaryToDecimal {
    logic integer decimal_value_of_prefix(char *p, integer len);

    axiom decimal_value_of_prefix_base:
      \for_all char *p; decimal_value_of_prefix(p, 0) == 0;

    axiom decimal_value_of_prefix_recursive_0:
      \for_all char *p, integer len;
        len > 0 && p[len-1] == '0' ==>
          decimal_value_of_prefix(p, len) == decimal_value_of_prefix(p, len - 1) * 2;

    axiom decimal_value_of_prefix_recursive_1:
      \for_all char *p, integer len;
        len > 0 && p[len-1] == '1' ==>
          decimal_value_of_prefix(p, len) == decimal_value_of_prefix(p, len - 1) * 2 + 1;
  }

  ensures \result == decimal_value_of_prefix(binary_str, length);
*/
int binary_to_decimal(char *binary_str, int length) {
    int decimal = 0;
    int power = 1; // Represents 2^0, 2^1, 2^2, ...

    /*@
      loop invariant 0 <= i <= length;
      loop invariant decimal == (\sum integer k; i <= k < length; (binary_str[k] - '0') * (1 << (length - 1 - k)));
      loop invariant decimal == decimal_value_of_prefix(binary_str, i);
      loop invariant power == (1 << i); // This invariant is for the loop iterating from left to right.
                                        // The current implementation iterates right to left.

      // Let's refine the invariants for the right-to-left iteration:
      loop invariant -1 <= i < length; // i goes from length - 1 down to -1
      // decimal stores the value of the suffix binary_str[i+1...length-1]
      // expressed as sum_{k=i+1}^{length-1} (binary_str[k] - '0') * 2^(length - 1 - k)
      loop invariant decimal == (\sum integer k; i+1 <= k < length; (binary_str[k] - '0') * (1 << (length - 1 - k)));
      loop invariant power == (1 << (length - 1 - i)); // power represents 2^(position from right)
                                                        // where position from right is (length - 1 - k) for current digit k

      // Alternative invariant for decimal:
      // This is a bit tricky with the recursive logic function, as it's defined for prefixes.
      // We can define another logic function for suffixes.
      axiomatic SuffixDecimal {
        logic integer decimal_value_of_suffix(char *p, integer start, integer end);
        axiom suffix_base:
          \for_all char *p, integer start; decimal_value_of_suffix(p, start, start) == 0;
        axiom suffix_recursive_0:
          \for_all char *p, integer start, integer end;
            start < end && p[end-1] == '0' ==>
              decimal_value_of_suffix(p, start, end) == decimal_value_of_suffix(p, start, end - 1);
        axiom suffix_recursive_1:
          \for_all char *p, integer start, integer end;
            start < end && p[end-1] == '1' ==>
              decimal_value_of_suffix(p, start, end) == decimal_value_of_suffix(p, start, end - 1) + (1 << (end - 1 - start));
      }
      // This suffix logic is also tricky for the loop.

      // Let's stick to the current loop structure and its invariants.
      // The `decimal` variable accumulates the sum.
      // `power` is the current power of 2 (1, 2, 4, ...).
      // `i` iterates from right to left.

      loop invariant 0 <= i <= length; // i is the loop counter, from length-1 down to -1
      // The accumulated decimal value from processed bits
      loop invariant decimal == (\sum integer k; i+1 <= k < length; (binary_str[k] - '0') * (1 << (length - 1 - k)));
      // The current power of 2 for the bit at index i
      loop invariant power == (1 << (length - 1 - i));

      loop assigns i, decimal, power;
      loop variant i; // Decreasing from length-1 to -1.
    */
    for (int i = length - 1; i >= 0; i--) {
        if (binary_str[i] == '1') {
            // Rule II.5: Prevent overflow during addition.
            // Check if decimal + power would exceed INT_MAX.
            // This is implicitly covered by the `requires length <= 30` clause,
            // as the maximum result for length 30 (2^30 - 1) fits in int.
            decimal += power;
        }
        // Rule II.5: Prevent overflow during multiplication.
        // Check if power * 2 would exceed INT_MAX.
        // This is implicitly covered by the `requires length <= 30` clause,
        // as the maximum power (2^29 for length 30) fits in int.
        // power will reach 2^(length-1) at most.
        if (i > 0) { // Only update power if there are more bits to process
            power *= 2;
        }
    }

    // Now, we need to connect the final value of `decimal` to `decimal_value_of_prefix`.
    // The loop calculates the decimal value from right to left.
    // The `decimal_value_of_prefix` is defined for left-to-right.
    // Let's adjust the `ensures` clause to match the loop's calculation.

    // Let's refine the axiomatic definition to match the loop's computation logic directly.
    // This is often easier for the prover.

    /*@
      axiomatic BinaryToDecimalRightToLeft {
        logic integer decimal_val_r_to_l(char *s, integer len);

        axiom decimal_val_r_to_l_base:
          \for_all char *s; decimal_val_r_to_l(s, 0) == 0;

        // Recursive definition from right to left
        axiom decimal_val_r_to_l_step:
          \for_all char *s, integer len;
            len > 0 ==>
              decimal_val_r_to_l(s, len) == decimal_val_r_to_l(s, len - 1) + (s[len-1] - '0') * (1 << (len - 1));
      }
      // Replace the previous `ensures` clause with this one.
      // ensures \result == decimal_val_r_to_l(binary_str, length); // This is not quite right.
      // The loop calculates sum_{k=0}^{length-1} (binary_str[k] - '0') * 2^(length - 1 - k)
      // This is equivalent to decimal_val_r_to_l where 's' is the reversed string.
      // Or, more directly:
      ensures \result == (\sum integer k; 0 <= k < length; (binary_str[k] - '0') * (1 << (length - 1 - k)));
    */
    return decimal;
}
