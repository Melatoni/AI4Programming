// Task ID: 33
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.5: Prevent potential overflow for `power_of_2` if `n` is too large.
  // Maximum value for `int` is typically 2,147,483,647.
  // 2^30 is 1,073,741,824. 2^31 would overflow.
  // So, `n` must be less than 2^31.
  // A safe upper bound for `n` to ensure `1 << i` doesn't overflow for `i < 31`.
  requires n >= 0;
  requires n < 2147483648; // Ensure n is within typical int range and allows 1 << 30

  // Rule II.2: Recursive logic for power of 2.
  // This axiomatic block defines a mathematical function `power_of_2`
  // and provides axioms for its behavior.
  axiomatic PowerOf2 {
    logic integer power_of_2(integer p);

    axiom power_of_2_base:
      power_of_2(0) == 1;

    axiom power_of_2_recursive:
      \forall integer p; p > 0 ==> power_of_2(p) == 2 * power_of_2(p - 1);

    // Rule II.2: Helper axiom to relate power_of_2 to bit shifts for verification.
    // This helps the prover understand the connection between `power_of_2` and `1 << i`.
    axiom power_of_2_shift:
      \forall integer p; p >= 0 && p < 31 ==> power_of_2(p) == (1 << p);
  }

  // Define a logic function to represent the decimal value of a binary sequence.
  // This is crucial for proving the correctness of the decimal to binary conversion.
  axiomatic BinToDec {
    logic integer bin_to_dec(int arr[], integer len);

    axiom bin_to_dec_base:
      bin_to_dec(arr, 0) == 0;

    axiom bin_to_dec_recursive:
      \forall int arr[], integer len; len > 0 ==>
        bin_to_dec(arr, len) == bin_to_dec(arr, len - 1) + arr[len - 1] * power_of_2(len - 1);
  }

  // The function `decimal_to_binary` converts a decimal number `n`
  // into its binary representation stored in the `binary_array`.
  // The `binary_array` is assumed to be large enough to hold the binary digits.
  // For `int` (32-bit signed), max bits needed is 31 (for positive numbers).
  requires \valid(binary_array + (0..30)); // Assuming max 31 bits for a positive int

  // The function returns the number of bits written to the array.
  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The result `num_bits` should be the smallest `k` such that `2^k > n` if `n > 0`, else 1.
  // The `binary_array` should contain the correct binary representation.
  ensures \result >= 0;
  ensures \result <= 31; // Max bits for a positive 32-bit integer

  // If n is 0, result is 1 and binary_array[0] is 0.
  ensures (n == 0) ==> (\result == 1 && binary_array[0] == 0);

  // If n > 0, the sum of array elements times their power of 2 should equal n.
  ensures (n > 0) ==> (bin_to_dec(binary_array, \result) == n);

  // Each element in the binary array should be either 0 or 1.
  ensures \forall integer k; 0 <= k < \result ==> (binary_array[k] == 0 || binary_array[k] == 1);

  assigns binary_array[0..30];
*/
int decimal_to_binary(int n, int binary_array[]) {
    if (n == 0) {
        binary_array[0] = 0;
        return 1; // 0 in binary is "0", which is 1 bit long.
    }

    int i = 0;
    /*@
      loop invariant 0 <= i;
      loop invariant n_copy >= 0;
      // The invariant below captures the core idea:
      // The original number `n` is equal to the sum of the bits already processed
      // plus the remaining `n_copy` multiplied by the current power of 2 (2^i).
      // This is crucial for establishing the post-condition.
      loop invariant n == bin_to_dec(binary_array, i) + n_copy * power_of_2(i);

      // Rule II.5: Loop invariant to prevent intermediate `n_copy` values from exceeding `int` max
      loop invariant n_copy <= 2147483647;

      loop assigns i, n_copy, binary_array[0..30];
      // Rule II.4: Loop variant for termination. The value of n_copy decreases (or becomes 0).
      // A more direct variant is `n_copy`.
      loop variant n_copy;
    */
    for (int n_copy = n; n_copy > 0; n_copy /= 2) {
        binary_array[i] = n_copy % 2;
        i++;
    }

    // The bits are generated in reverse order (least significant first).
    // Now, we need to reverse the array to get the standard binary representation.
    int left = 0;
    int right = i - 1;

    /*@
      loop invariant 0 <= left;
      loop invariant left <= right + 1; // left can be equal to right + 1 when loop finishes
      loop invariant right == \at(i, LoopEntry) - 1 - (left - \at(left, LoopEntry));
      loop invariant \forall integer k; 0 <= k < left ==> (binary_array[k] == \at(binary_array[\at(i, LoopEntry) - 1 - k], LoopEntry));
      loop invariant \forall integer k; right < k < \at(i, LoopEntry) ==> (binary_array[k] == \at(binary_array[\at(i, LoopEntry) - 1 - k], LoopEntry));
      loop invariant \forall integer k; left <= k <= right ==> (binary_array[k] == \at(binary_array[k], LoopEntry));

      loop assigns left, right, binary_array[0..30];
      // Rule II.4: Loop variant for termination. The distance between left and right decreases.
      loop variant right - left;
    */
    while (left < right) {
        int temp = binary_array[left];
        binary_array[left] = binary_array[right];
        binary_array[right] = temp;
        left++;
        right--;
    }

    return i; // i now holds the number of bits.
}
