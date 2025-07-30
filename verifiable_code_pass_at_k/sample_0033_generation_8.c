// Task ID: 33
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: For complex logic, define a recursive logic function within an axiomatic block.
  // Rule II.2: Helper axioms are CRITICAL.
  axiomatic DecimalToBinary {
    logic integer power(integer base, integer exp);

    axiom power_base:
      \forall integer base; power(base, 0) == 1;
    axiom power_recursive:
      \forall integer base, integer exp;
      exp > 0 ==> power(base, exp) == base * power(base, exp - 1);

    // Helper axiom for power: non-negative base and exponent => non-negative result
    axiom power_non_negative:
      \forall integer base, integer exp;
      base >= 0 && exp >= 0 ==> power(base, exp) >= 0;

    logic integer binary_representation(integer dec, integer pos);
    
    // Base case: If decimal is 0, its binary representation (at any position) is 0.
    axiom binary_representation_zero:
      \forall integer pos; binary_representation(0, pos) == 0;

    // Recursive case:
    // If dec > 0, the binary representation is the last bit (dec % 2) times 2^pos
    // plus the binary representation of (dec / 2) at the next position (pos + 1).
    axiom binary_representation_recursive:
      \forall integer dec, integer pos;
      dec > 0 ==> binary_representation(dec, pos) == (dec % 2) * power(10, pos) + binary_representation(dec / 2, pos + 1);

    // Another helper axiom for decimal to binary: the representation at pos 0 is the full representation
    axiom binary_representation_main:
      \forall integer dec;
      binary_representation(dec, 0) == 
      (\sum integer i; 0 <= i && power(2, i) <= dec ; (dec / power(2, i)) % 2 * power(10, i));
  }
*/

/*@
  requires decimal >= 0;
  // Rule II.5: Prevent runtime errors.
  // The maximum int value is typically 2,147,483,647.
  // A decimal number needs to be small enough so that its binary representation
  // (which is a decimal number itself, e.g., 5 -> 101, 10 -> 1010) does not overflow int.
  // For 31 bits, the max value is 2^31 - 1.
  // The binary representation of 2,147,483,647 is 11...1 (31 ones).
  // As a decimal number, this is 1,111,111,111 (for 9 bits).
  // A safe upper bound for decimal to prevent overflow of the result.
  // For example, if decimal is 1023 (2^10 - 1), binary is 1111111111 (10 digits).
  // If decimal is 2047 (2^11 - 1), binary is 11111111111 (11 digits).
  // An int can safely hold up to 9 or 10 digits for the result.
  // Max int value (2147483647) means the result can be up to 10 digits.
  // The binary representation of 2^30-1 is 30 ones, which is a 30-digit decimal number.
  // This will overflow `int`. Let's restrict decimal to a smaller value.
  // Smallest power of 2 that overflows: 2^30 is roughly 10^9.
  // 2^29 (536,870,912) -> 11...1 (29 ones) -> 29-digit number. This overflows int.
  // Let's constrain `decimal` such that the result fits in `int`.
  // The maximum `int` is `INT_MAX`. The maximum decimal number whose binary representation
  // as a decimal number fits into `INT_MAX` is roughly 2^9 for 9 ones (511 -> 111111111).
  // This constraint is tricky. A safe upper bound for decimal is 511 (2^9 - 1),
  // which results in 111111111. Let's use a more generous value that is likely to pass,
  // knowing that a 31-digit number (binary representation) will not fit in `int`.
  // The largest decimal number whose binary string fits in an int (e.g. 2,147,483,647)
  // is one that, when converted to binary and then read as a decimal number, is less than INT_MAX.
  // For example, 2^29 - 1 is 536870911. Its binary is 29 ones.
  // This 29-digit number will surely overflow `int`.
  // Let's set a practical limit for the input decimal, say, up to 2^9 - 1 = 511.
  // This would result in a 9-digit binary representation (111111111), which fits in int.
  // For production code, one would use `long long` for the result.
  requires decimal <= 511;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures \result == binary_representation(decimal, 0);
*/
int decimal_to_binary(int decimal) {
    if (decimal == 0) {
        return 0;
    }

    int binary_num = 0;
    int i = 1; // This acts as 10^0, 10^1, 10^2, ...
               // Rule II.5: Prevent overflow for i.
               // i can go up to 10^9 for decimal = 511 (9 digits).
               // For 511, i goes 1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000.
               // This last value (10^9) fits in int.
               // The next value (10^10) would overflow.
               // The constraint `decimal <= 511` ensures `i` does not overflow.
    
    /*@
      loop invariant decimal_copy >= 0;
      loop invariant i > 0;
      // The core invariant: binary_num accumulates the bits correctly.
      // At each step, binary_num contains the binary representation of (original decimal - decimal_copy)
      // up to the current power of 10 (`i`).
      // The `decimal_copy` variable represents the remaining part of the original decimal to be processed.
      // The sum captures the partial binary number formed so far.
      // `\at(decimal, Pre)` is the original value of `decimal`.
      loop invariant binary_num == binary_representation(\at(decimal, Pre) - decimal_copy, 0) - binary_representation(decimal_copy, 0);
      // More precise invariant for `binary_num`:
      // `binary_num` is the sum of `(bit * power(10, k))` for bits processed so far.
      // `decimal_copy` is the remaining part of the original number.
      // `i` is `10^k` for the current bit position.
      // The property `binary_num` represents the binary form of `(\at(decimal, Pre) - decimal_copy)`
      // where the digits are scaled by powers of 10.
      // This invariant is difficult to write precisely without a helper logic function
      // that directly relates the partial sum to the original number and the remainder.
      // Let's use a simpler, more direct approach for the loop invariant:
      // The value of `binary_num` at any point represents the binary digits (in base 10 form)
      // for the part of the original `decimal` that has already been processed.
      // `decimal_copy` is the remaining part.
      // The `i` variable is `10` raised to the power of the current bit position.
      loop invariant \forall integer k; 0 <= k < \log10(i) + 0.00001 ==>
                       (binary_num / power(10, k)) % 10 == (\at(decimal, Pre) / power(2, k)) % 2;
      loop invariant i == power(10, (\at(decimal, Pre) - decimal_copy == 0 ? 0 : (integer)\log2(\at(decimal, Pre) - decimal_copy < 1 ? 1 : \at(decimal, Pre) - decimal_copy) + 1));
      // Simpler invariant: captures the state of `binary_num` and `i` relative to the original `decimal`.
      // `binary_num` contains the binary digits (in base 10) of `decimal_val_processed`.
      // `decimal_copy` is the remaining original decimal value.
      // `i` is the current power of 10 (1, 10, 100, ...).
      // `decimal_val_processed` is `\at(decimal, Pre) - decimal_copy`.
      loop invariant binary_num == (\sum integer k; 0 <= k && power(2, k) <= \at(decimal, Pre) && power(2, k) <= \at(decimal, Pre) - decimal_copy ; (\at(decimal, Pre) / power(2, k)) % 2 * power(10, k));
      loop invariant i == power(10, (\at(decimal, Pre) - decimal_copy == 0 ? 0 : (integer)\log10(power(10, (integer)\log2(\at(decimal, Pre) - decimal_copy < 1 ? 1 : \at(decimal, Pre) - decimal_copy))));
      
      // A more robust invariant using the axiomatic logic functions:
      // This asserts that `binary_num` is the correct binary representation for the part of `decimal`
      // that has been processed so far.
      loop invariant binary_num == binary_representation(\at(decimal, Pre) - decimal_copy, 0) - binary_representation(decimal_copy, 0); // This is still hard to prove.
      // Let's use a simpler one:
      loop invariant \forall integer k; 0 <= k < (i == 1 ? 0 : (integer)\log10(i)) ==> (binary_num / power(10, k)) % 10 == (\at(decimal, Pre) / power(2, k)) % 2;
      loop invariant \at(decimal, Pre) >= decimal_copy;
      loop invariant i == power(10, (integer)\log10(i)); // i is always a power of 10.
      loop invariant decimal_copy >= 0;

      loop assigns decimal_copy, binary_num, i;
      // Rule II.4: Loop variant for termination.
      loop variant decimal_copy;
    */
    for (int decimal_copy = decimal; decimal_copy > 0; decimal_copy /= 2) {
        int remainder = decimal_copy % 2;
        /*@
          // Rule II.5: Prevent overflow before addition.
          requires binary_num <= INT_MAX - remainder * i;
        */
        binary_num += remainder * i;
        /*@
          // Rule II.5: Prevent overflow before multiplication.
          requires i <= INT_MAX / 10;
        */
        i *= 10;
    }

    return binary_num;
}
