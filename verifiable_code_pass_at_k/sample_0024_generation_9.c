// Task ID: 24
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in axiomatic block.

  // Rule II.1: Recursive logic for summation.
  // Rule II.2: Helper axioms for properties.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic Power {
    logic integer power(integer base, integer exp);

    axiom power_base:
      \forall integer base; power(base, 0) == 1;

    axiom power_rec:
      \forall integer base, exp;
      exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

    // Rule II.2: Helper axiom for a common power property.
    // This helps prove that power(2, exp) remains positive.
    axiom power_positive:
      \forall integer base, exp;
      base > 0 && exp >= 0 ==> power(base, exp) > 0;
  }
*/

/*@
  axiomatic BinaryToDecimal {
    // Rule I.3: For array parameters T arr[R][C], remember they decay to pointers T (*arr)[C].
    // Here, `arr` is `int*` because it's a 1D array.
    logic integer binary_to_decimal_logic(int* binary_digits, integer len, integer k);

    // Base case: If k reaches len, there are no more digits to process.
    axiom binary_to_decimal_base:
      \forall int* binary_digits, integer len;
      binary_to_decimal_logic(binary_digits, len, len) == 0;

    // Recursive case: Sum of (digit * 2^position)
    axiom binary_to_decimal_rec:
      \forall int* binary_digits, integer len, integer k;
      0 <= k < len ==>
      binary_to_decimal_logic(binary_digits, len, k) ==
        binary_digits[k] * power(2, len - 1 - k) + binary_to_decimal_logic(binary_digits, len, k + 1);

    // Helper axiom: The total decimal value is the sum from index 0.
    // This helps connect the recursive definition to the overall result.
    axiom binary_to_decimal_total:
      \forall int* binary_digits, integer len;
      (\forall integer i; 0 <= i < len ==> (binary_digits[i] == 0 || binary_digits[i] == 1)) ==>
      binary_to_decimal_logic(binary_digits, len, 0) ==
        (\sum integer i; 0 <= i < len; binary_digits[i] * power(2, len - 1 - i));
  }
*/

/*@
  requires len > 0;
  requires len <= 31; // Rule II.5: Prevent overflow for 2^len. Max 2^30 for int.
  requires \valid_read_range(binary_digits, 0, len - 1);
  requires \forall integer i; 0 <= i < len ==> (binary_digits[i] == 0 || binary_digits[i] == 1);

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function returns the decimal value directly, so no boolean equivalence needed here.
  ensures \result == binary_to_decimal_logic(binary_digits, len, 0);
  ensures \result >= 0; // The decimal equivalent of a binary number is always non-negative.
*/
int binary_to_decimal(int* binary_digits, int len) {
    int decimal_value = 0;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant decimal_value == binary_to_decimal_logic(binary_digits, len, i);
      loop invariant \forall integer k; 0 <= k < i ==> (binary_digits[k] == 0 || binary_digits[k] == 1);
      loop assigns i, decimal_value;
      loop variant len - i; // Rule II.4: A loop variant is mandatory for termination.
    */
    for (int i = 0; i < len; i++) {
        // Rule II.5: Prevent overflow during multiplication.
        // The maximum value for decimal_value is (2^len - 1).
        // Max len is 31, so max value is 2^31 - 1, which fits in int.
        // We need to ensure that decimal_value * 2 does not overflow.
        // Since len <= 31, decimal_value * 2 will not exceed 2^31, which fits within signed int range.
        // The addition of binary_digits[i] is either 0 or 1, not causing overflow.
        decimal_value = decimal_value * 2 + binary_digits[i];
    }
    return decimal_value;
}
