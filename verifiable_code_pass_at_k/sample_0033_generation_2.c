// Task ID: 33
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Problem: Convert a decimal number to binary.
  // Since C does not have arbitrary-precision integers, we will
  // represent the binary number as an array of integers (0 or 1).
  // The function will return the number of bits in the binary representation.

  // Rule II.1: Define recursive logic for properties over sequences.
  // This axiomatic block defines the mathematical interpretation of the binary array.
*/
/*@
  axiomatic BinaryRepresentation {
    logic integer power(integer base, integer exp);

    axiom power_base:
      \forall integer base; power(base, 0) == 1;
    axiom power_rec:
      \forall integer base, integer exp;
      exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

    // This function calculates the decimal value of a binary array.
    // bits[0] is the LSB, bits[size-1] is the MSB.
    logic integer decimal_value(int* bits, integer size);

    axiom decimal_value_base:
      decimal_value(bits, 0) == 0;
    axiom decimal_value_rec:
      \forall int* bits, integer size;
      size > 0 ==> decimal_value(bits, size) == bits[size - 1] * power(2, size - 1) + decimal_value(bits, size - 1);

    // Rule II.2: Helper axioms for the recursive logic.
    // This helper axiom ensures that each bit is either 0 or 1.
    axiom decimal_value_bits_valid:
      \forall int* bits, integer size;
      (\forall integer i; 0 <= i < size ==> (bits[i] == 0 || bits[i] == 1)) ==>
      decimal_value(bits, size) >= 0; // The value must be non-negative if bits are 0/1.

    // A more specific helper axiom for the problem.
    // If all bits are 0 or 1, and the value is computed correctly,
    // then the decimal value must be accurate.
    // This is implicitly covered by the definition, but good to have a thought process for it.
  }
*/

/*@
  requires num >= 0;
  // Rule II.5: Prevent runtime errors.
  // Max number of bits for a 32-bit int is 31 (for num > 0), plus one for 0.
  // A buffer of 32 bits is sufficient.
  requires max_len >= 32; // Assuming num is a 32-bit integer.
  requires \valid_range(binary_arr, 0, max_len - 1);
  // Rule II.5: Ensure bits are initialized to 0 or 1 if they were not.
  // Or, more practically, ensure they are 0 for unused parts.
  // For this function, it will write 0s and 1s, so no pre-condition on content.

  assigns binary_arr[0..max_len-1];

  // Rule II.3: Ensures clause uses logical equivalence.
  // The function returns the number of bits used.
  // The decimal value represented by the first `\result` bits of `binary_arr`
  // must be equal to the input `num`.
  ensures \forall integer i; 0 <= i < \result ==> (binary_arr[i] == 0 || binary_arr[i] == 1);
  ensures \result == 0 <==> num == 0; // Special case for num = 0
  ensures \result > 0 ==> decimal_value(binary_arr, \result) == num;
  // Ensure that bits beyond the result are 0 (or undefined, but 0 is safer).
  ensures \forall integer i; \result <= i < max_len ==> binary_arr[i] == 0;
  // Ensure the result is within bounds.
  ensures 0 <= \result <= max_len;
*/
int decimal_to_binary(int num, int* binary_arr, int max_len) {
    int i = 0;
    // Special case for num = 0
    if (num == 0) {
        /*@
          loop invariant \forall integer k; i <= k < max_len ==> binary_arr[k] == 0;
          loop assigns binary_arr[i];
          loop variant max_len - i;
        */
        for (i = 0; i < max_len; ++i) {
            binary_arr[i] = 0;
        }
        return 0;
    }

    /*@
      // Rule II.4: Mandatory loop invariants and variant.
      loop invariant 0 <= i < max_len;
      // The decimal value of the bits processed so far, plus the remaining `num`,
      // should equal the original number.
      // This is a common invariant for conversion algorithms.
      // Rule III.2: No parentheses around if-then-else.
      loop invariant (decimal_value(binary_arr, i) + num * power(2, i)) == \old(num);
      loop invariant \forall integer k; 0 <= k < i ==> (binary_arr[k] == 0 || binary_arr[k] == 1);
      loop invariant num >= 0; // num remains non-negative
      loop assigns num, i, binary_arr[0..i-1];
      loop variant num; // num decreases strictly
    */
    while (num > 0 && i < max_len) {
        binary_arr[i] = num % 2;
        num = num / 2;
        i++;
    }

    // Fill the rest of the array with zeros
    /*@
      loop invariant i <= max_len;
      loop invariant \forall integer k; \old(i) <= k < i ==> binary_arr[k] == 0;
      loop assigns binary_arr[i];
      loop variant max_len - i;
    */
    while (i < max_len) {
        binary_arr[i] = 0;
        i++;
    }

    return \old(i); // Return the number of bits used before zero-padding
}
