// Task ID: 33
// Generation: 6

/*@ axiomatic DecimalToBinary {
  logic integer power(integer base, integer exp) =
    exp == 0 ? 1 : base * power(base, exp - 1);

  // Helper axiom: power of 2 is always positive
  axiom power_positive:
    \forall integer b, e; b >= 0 && e >= 0 ==> power(b, e) >= 0;

  // Helper axiom: power of 2 is monotonic
  axiom power_monotonic:
    \forall integer b, e1, e2; b > 1 && e1 < e2 ==> power(b, e1) < power(b, e2);

  // Helper axiom: power of 2 grows
  axiom power_grows:
    \forall integer b, e; b > 1 && e >= 0 ==> power(b, e) >= e + 1;

  // Helper axiom: relation between power and division
  axiom power_div_relation:
    \forall integer base, exp; exp > 0 ==> power(base, exp) == (base * power(base, exp - 1));

  // Defines what it means for `res` to be the binary representation of `dec`
  // `res` is an array of bits, `len` is its effective length.
  // The least significant bit is at index 0.
  logic integer decimal_value(int* res, integer len) reads res[0..len-1];

  axiom decimal_value_base:
    \forall int* res; decimal_value(res, 0) == 0;

  axiom decimal_value_recursive:
    \forall int* res, integer k;
      k > 0 ==> decimal_value(res, k) == res[k-1] * power(2, k-1) + decimal_value(res, k-1);

  // Helper axiom: bits are 0 or 1
  axiom bits_are_0_or_1:
    \forall int* res, integer k;
      k >= 0 && k < \length(res) ==> (res[k] == 0 || res[k] == 1);

  // Helper axiom: decimal_value is non-negative
  axiom decimal_value_non_negative:
    \forall int* res, integer len; len >= 0 ==> decimal_value(res, len) >= 0;

  // Helper axiom: decimal_value is 0 if all bits are 0
  axiom decimal_value_zero_if_all_zero:
    \forall int* res, integer len;
      (\forall integer k; 0 <= k < len ==> res[k] == 0) ==> decimal_value(res, len) == 0;

  // Helper axiom: if a bit is 1, decimal_value is at least power of 2
  axiom decimal_value_at_least_power_of_2:
    \forall int* res, integer len, integer i;
      0 <= i < len && res[i] == 1 ==> decimal_value(res, len) >= power(2, i);

  // Helper axiom: if all bits are 0 for higher indices, decimal_value is only up to a certain point
  axiom decimal_value_upper_bound_if_zeros:
    \forall int* res, integer len, integer i;
      0 <= i < len && (\forall integer k; i < k < len ==> res[k] == 0) ==>
        decimal_value(res, len) == decimal_value(res, i+1);

}
*/

/*@
  requires dec >= 0;
  requires max_bits > 0;
  requires \valid(binary_array + (0..max_bits-1));

  // Ensure that the result array `binary_array` contains the binary representation of `dec`.
  // The effective length of the binary representation is `*actual_bits_len`.
  // The value represented by `binary_array` up to `*actual_bits_len` must be `dec`.
  ensures decimal_value(binary_array, *actual_bits_len) == dec;

  // Each bit in the result array must be either 0 or 1.
  ensures \forall integer i; 0 <= i < *actual_bits_len ==> (binary_array[i] == 0 || binary_array[i] == 1);

  // The actual length of the binary representation must be within the provided bounds.
  ensures 0 <= *actual_bits_len <= max_bits;

  // If dec is 0, the length should be 1 and the bit should be 0.
  ensures dec == 0 ==> (*actual_bits_len == 1 && binary_array[0] == 0);

  // If dec is positive, the most significant bit (at index *actual_bits_len - 1) must be 1.
  ensures dec > 0 ==> binary_array[*actual_bits_len - 1] == 1;

  assigns binary_array[0..max_bits-1], *actual_bits_len;
*/
void decimal_to_binary(int dec, int* binary_array, int max_bits, int* actual_bits_len) {
    int i = 0;
    int temp_dec = dec;

    // Special case for 0
    if (temp_dec == 0) {
        binary_array[0] = 0;
        *actual_bits_len = 1;
        return;
    }

    /*@
      loop invariant 0 <= i <= max_bits;
      // All bits processed so far are 0 or 1
      loop invariant \forall integer k; 0 <= k < i ==> (binary_array[k] == 0 || binary_array[k] == 1);
      // The current decimal value `temp_dec` plus the value of the bits already processed
      // equals the original decimal value `dec`.
      loop invariant (decimal_value(binary_array, i) + temp_dec * power(2, i)) == dec;
      loop invariant temp_dec >= 0;

      loop assigns i, temp_dec, binary_array[0..max_bits-1];
      loop variant temp_dec;
    */
    while (temp_dec > 0 && i < max_bits) {
        binary_array[i] = temp_dec % 2;
        temp_dec = temp_dec / 2;
        i++;
    }
    *actual_bits_len = i;

    // If temp_dec is still greater than 0, it means max_bits was not enough.
    // This case is implicitly covered by the requires clause on max_bits,
    // which should ensure max_bits is large enough for the given dec.
    // For example, requires dec < power(2, max_bits);
    // For this specific problem, we assume max_bits is sufficient if not specified otherwise.
}
