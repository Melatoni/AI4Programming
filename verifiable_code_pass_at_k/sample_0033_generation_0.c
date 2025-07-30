// Task ID: 33
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax (0..n-1).
  // Rule III.4: No stray semicolons.
*/

/*@ axiomatic DecimalToBinary {
  logic integer power(integer base, integer exp) =
    if exp == 0 then 1
    else base * power(base, exp - 1);

  // Helper axiom: power of 2 is always positive for non-negative exponent
  axiom power_positive:
    \forall integer exp; exp >= 0 ==> power(2, exp) >= 1;

  // Helper axiom: power of 2 grows with exponent
  axiom power_monotonic:
    \forall integer exp1, exp2; exp1 >= 0 && exp2 >= 0 && exp1 < exp2 ==> power(2, exp1) < power(2, exp2);

  // Helper axiom: relationship between power and division
  axiom power_division_property:
    \forall integer n, p; n >= 0 && p >= 0 && power(2, p) <= n ==> power(2, p) <= n;

  // Helper axiom: division by power of 2
  axiom div_by_power_of_2:
    \forall integer n, p; n >= 0 && p >= 0 ==> n / power(2, p) == (n >> p);

  // Helper axiom: modulo by power of 2
  axiom mod_by_power_of_2:
    \forall integer n, p; n >= 0 && p >= 0 ==> n % power(2, p) == (n & (power(2, p) - 1));

  // Recursive logic function to represent the decimal number as a sum of powers of 2.
  // This represents the value of the binary array.
  logic integer binary_to_decimal(int* binary_arr, integer size) reads binary_arr[0..size-1];

  axiom binary_to_decimal_base:
    \forall int* binary_arr; binary_to_decimal(binary_arr, 0) == 0;

  axiom binary_to_decimal_recursive:
    \forall int* binary_arr, integer size; size > 0 ==>
      binary_to_decimal(binary_arr, size) ==
      binary_to_decimal(binary_arr, size - 1) + (binary_arr[size - 1] * power(2, size - 1));

  // Helper axiom: each bit is 0 or 1
  axiom binary_bit_valid:
    \forall int* binary_arr, integer size, integer i;
      0 <= i < size && (binary_arr[i] == 0 || binary_arr[i] == 1) ==>
      (binary_arr[i] * power(2, i) >= 0);

  // Helper axiom: sum of bits is non-negative
  axiom binary_to_decimal_non_negative:
    \forall int* binary_arr, integer size;
      (\forall integer i; 0 <= i < size ==> (binary_arr[i] == 0 || binary_arr[i] == 1)) ==>
      binary_to_decimal(binary_arr, size) >= 0;

  // Helper axiom: upper bound for binary_to_decimal
  axiom binary_to_decimal_upper_bound:
    \forall int* binary_arr, integer size;
      (\forall integer i; 0 <= i < size ==> (binary_arr[i] == 0 || binary_arr[i] == 1)) ==>
      binary_to_decimal(binary_arr, size) <= power(2, size) - 1;

  // Helper axiom: lower bound for binary_to_decimal
  axiom binary_to_decimal_lower_bound:
    \forall int* binary_arr, integer size;
      (\forall integer i; 0 <= i < size ==> (binary_arr[i] == 0 || binary_arr[i] == 1)) ==>
      binary_to_decimal(binary_arr, size) >= 0;

  // Helper axiom: if a bit is 1, it contributes to the sum
  axiom binary_bit_contribution:
    \forall int* binary_arr, integer size, integer i;
      0 <= i < size && binary_arr[i] == 1 ==>
      binary_to_decimal(binary_arr, size) >= power(2, i);

  // Helper axiom: if a bit is 0, it does not contribute to the sum for that position
  axiom binary_bit_no_contribution:
    \forall int* binary_arr, integer size, integer i;
      0 <= i < size && binary_arr[i] == 0 ==>
      binary_to_decimal(binary_arr, size) - (binary_arr[i] * power(2, i)) == binary_to_decimal(binary_arr, size);

}
*/

/*@
  requires n >= 0;
  requires n <= 2147483647; // Max value for int to prevent overflow during calculations
  requires max_bits > 0;
  requires max_bits <= 31; // Max bits for a 32-bit integer, to avoid issues with power(2, max_bits)
  requires \valid_range(binary_arr, 0, max_bits - 1); // binary_arr must be writable
  
  assigns binary_arr[0..max_bits-1];
  
  // Rule II.3: Ensures clause uses logical equivalence for boolean-like return (number of bits used).
  ensures \result >= 0 && \result <= max_bits;
  ensures (\forall integer i; 0 <= i < \result ==> (binary_arr[i] == 0 || binary_arr[i] == 1));
  ensures (\forall integer i; \result <= i < max_bits ==> binary_arr[i] == 0); // Unused bits are zeroed out
  ensures binary_to_decimal(binary_arr, \result) == n;
  ensures n == 0 <==> \result == 0;
*/
int decimal_to_binary(int n, int* binary_arr, int max_bits) {
    int i = 0;
    int temp_n = n;

    // Initialize the array to all zeros
    /*@
      loop invariant 0 <= i <= max_bits;
      loop invariant \forall integer k; 0 <= k < i ==> binary_arr[k] == 0;
      loop assigns i, binary_arr[0..max_bits-1];
      loop variant max_bits - i;
    */
    for (i = 0; i < max_bits; i++) {
        binary_arr[i] = 0;
    }

    i = 0; // Reset i for the conversion loop

    /*@
      loop invariant 0 <= i <= max_bits;
      loop invariant temp_n >= 0;
      // The value represented by the bits processed so far plus the remaining temp_n should equal original n.
      loop invariant (binary_to_decimal(binary_arr, i) + temp_n) == n;
      loop invariant \forall integer k; 0 <= k < i ==> (binary_arr[k] == 0 || binary_arr[k] == 1);
      loop invariant \forall integer k; i <= k < max_bits ==> binary_arr[k] == 0; // Unprocessed bits are zero.

      loop assigns i, temp_n, binary_arr[0..max_bits-1];
      loop variant temp_n; // temp_n strictly decreases
    */
    while (temp_n > 0 && i < max_bits) {
        binary_arr[i] = temp_n % 2;
        temp_n = temp_n / 2;
        i++;
    }

    return i; // Return the number of bits used
}
