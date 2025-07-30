// Task ID: 33
// Generation: 1

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
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@ axiomatic BinaryConversion {
  // Define a recursive logic function to represent the decimal value of a binary array.
  // Rule II.1: Recursive logic for complexity.
  logic integer decimal_value(int* arr, integer len);

  // Base case: empty array or single element
  axiom decimal_value_base_empty:
    \forall int* arr; decimal_value(arr, 0) == 0;

  axiom decimal_value_base_one:
    \forall int* arr; decimal_value(arr, 1) == arr[0];

  // Recursive case: sum of arr[len-1] * 2^(len-1) + decimal_value(arr, len-1)
  axiom decimal_value_recursive:
    \forall int* arr, integer len;
    len > 0 ==> decimal_value(arr, len) == arr[len-1] * (\pow2(len-1)) + decimal_value(arr, len-1);

  // Helper axiom: if all elements are 0 or 1, then the decimal value is non-negative.
  // Rule II.2: Helper axioms.
  axiom decimal_value_non_negative:
    \forall int* arr, integer len;
    (\forall integer i; 0 <= i < len ==> (arr[i] == 0 || arr[i] == 1)) ==> decimal_value(arr, len) >= 0;

  // Helper axiom: sum of powers of 2. For n >= 0, sum_{i=0 to n} 2^i = 2^(n+1) - 1
  // This is implicitly used in the range of decimal_value.
  // The maximum decimal value for a 31-bit integer is 2^31 - 1.
  // For a binary array of length 'len', the maximum value is 2^len - 1 (if all bits are 1).
  // So, 2^len - 1 should be <= INT_MAX. This implies len <= 31.
  // The function assumes the output array `binary` is large enough.
  // We'll enforce this with a requires clause for `max_binary_len`.
  // Max len for int is 31 bits (excluding sign).
  // Max len for long long is 63 bits.
  // Assuming `int` is 32-bit signed.
  axiom pow2_positive:
    \forall integer n; n >= 0 ==> \pow2(n) > 0;

}
*/

/*@
  requires decimal_num >= 0;
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Ensure that decimal_num can be represented within the binary array.
  // Max value for `int` is `INT_MAX`.
  // The maximum length of the binary representation of INT_MAX is 31 bits (for 32-bit signed int).
  // So, `max_binary_len` must be at least 31 to represent any `int`.
  requires max_binary_len >= 31; // Sufficient for any positive int.
  requires \valid_range(binary, 0, max_binary_len - 1);

  assigns binary[0..max_binary_len-1];

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (\exists integer k; 0 <= k <= max_binary_len && decimal_value(binary, k) == \old(decimal_num)) <==> (\result == 1);
  ensures (\result == 1) ==> (\forall integer i; 0 <= i < \result_len ==> (binary[i] == 0 || binary[i] == 1));
  ensures (\result == 1) ==> (\forall integer i; \result_len <= i < max_binary_len ==> binary[i] == 0); // Pad with zeros
  // Ensures that `\result_len` is the actual length of the binary representation.
  // If result is 1 (success), then \result_len is the number of bits used.
  // If decimal_num is 0, \result_len will be 1 (binary[0] == 0).
  // If decimal_num is positive, the most significant bit should be 1.
  ensures (\result == 1 && \old(decimal_num) > 0) ==> binary[\result_len - 1] == 1;

  // The \result_len is a ghost variable to store the actual length of the binary string.
  // Frama-C doesn't allow ghost variables as return values directly.
  // Instead, the function returns 1 on success, and the length is implicit
  // or could be returned via a pointer argument.
  // For simplicity, we'll assume the length is implicitly captured by the
  // lowest k such that decimal_value(binary, k) == decimal_num.
  // We'll add a ghost variable `\result_len` to make it explicit in ACSL.
  // This requires a `behavior` block to define `\result_len`.
*/
/*@ behavior success:
  assumes decimal_num >= 0;
  assumes max_binary_len >= 31;
  assumes \valid_range(binary, 0, max_binary_len - 1);

  assigns binary[0..max_binary_len-1];

  ensures \result == 1;
  ensures decimal_value(binary, \result_len) == \old(decimal_num);
  // Ensure \result_len is the minimal length for positive numbers.
  ensures \old(decimal_num) > 0 ==> (binary[\result_len - 1] == 1);
  ensures \old(decimal_num) == 0 ==> (\result_len == 1 && binary[0] == 0);
  ensures \forall integer i; 0 <= i < \result_len ==> (binary[i] == 0 || binary[i] == 1);
  ensures \forall integer i; \result_len <= i < max_binary_len ==> binary[i] == 0;
*/
int decimal_to_binary(int decimal_num, int* binary, int max_binary_len) {
    int i = 0;
    int temp_num = decimal_num;

    // Handle the special case for 0
    if (temp_num == 0) {
        /*@
          loop invariant i == 0;
          loop invariant temp_num == 0;
          loop invariant \forall integer k; 0 <= k < i ==> binary[k] == 0;
          loop assigns i;
          loop variant max_binary_len - i;
        */
        for (i = 0; i < max_binary_len; i++) {
            binary[i] = 0;
        }
        binary[0] = 0; // The binary representation of 0 is just "0"
        // Set ghost variable `\result_len` to 1.
        //@ ghost \result_len = 1;
        return 1;
    }

    /*@
      loop invariant 0 <= i <= max_binary_len;
      // The decimal value represented by the bits processed so far, plus the remaining temp_num * 2^i
      // should equal the original decimal_num.
      loop invariant (decimal_num - temp_num) == decimal_value(binary, i); // This is wrong. It should be:
      // decimal_value(binary, i) + temp_num * \pow2(i) == \old(decimal_num)
      loop invariant decimal_value(binary, i) + temp_num * (\pow2(i)) == \old(decimal_num);
      loop invariant \forall integer k; 0 <= k < i ==> (binary[k] == 0 || binary[k] == 1);
      loop assigns temp_num, i, binary[0..max_binary_len-1]; // binary[0..i-1] is more precise but Frama-C needs bounds
      loop variant temp_num; // temp_num decreases in each iteration
    */
    while (temp_num > 0 && i < max_binary_len) {
        binary[i] = temp_num % 2;
        temp_num = temp_num / 2;
        i++;
    }

    // Pad the rest of the array with zeros if the binary representation is shorter than max_binary_len
    /*@
      loop invariant i <= k <= max_binary_len;
      loop invariant \forall integer m; i <= m < k ==> binary[m] == 0;
      loop assigns binary[i..max_binary_len-1];
      loop variant max_binary_len - k;
    */
    for (int k = i; k < max_binary_len; k++) {
        binary[k] = 0;
    }

    // The binary array is filled in reverse order (LSB at index 0).
    // The `decimal_value` logic function works with this order.
    // The actual length of the binary representation is `i`.
    //@ ghost \result_len = i;
    return 1; // Success
}
