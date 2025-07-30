// Task ID: 33
// Generation: 5

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Use int for boolean-like return values.
  // Rule II.5: Prevent potential overflow for n when converting.
  // Assuming n is a non-negative integer.
  requires n >= 0;
  // Maximum n such that 2^31-1 (INT_MAX) bits are enough.
  // 31 is the max number of bits for a signed int.
  // For example, if n = 2^30, then the loop will run 31 times.
  // This constraint is more about the output array size rather than n itself.
  // However, for the purpose of conversion, n should not exceed INT_MAX.
  // The result array should be large enough to hold all bits.
  // A typical int is 32-bit, so it can hold up to 2^31-1.
  // log2(2^31-1) approx 30.9. So 31 bits are needed for the value, plus sign.
  // Let's assume the max number of bits needed is 31 for positive numbers.
  // The size of the array `binaryNum` should be at least 31.
  // For this problem, we are asked to convert a decimal number to binary.
  // The output is an array of bits.
  // We need to define the maximum size of the binary array.
  // Let's assume an int is 32-bit. So, max 32 bits are needed for the result.
  // The caller must provide an array of sufficient size.
  // The function returns the number of bits in the binary representation.

  // Rule II.1: Recursive logic for complexity.
  // Defines the value represented by a binary array segment.
  axiomatic BinaryValue {
    logic integer binary_value_segment(int* arr, integer start, integer end);

    // Rule II.2: Base case for recursive logic.
    axiom binary_value_segment_base:
      \forall int* arr, integer start;
        binary_value_segment(arr, start, start) == 0;

    // Rule II.2: Recursive step for recursive logic.
    axiom binary_value_segment_recursive:
      \forall int* arr, integer start, integer end;
        end > start ==>
        binary_value_segment(arr, start, end) ==
          binary_value_segment(arr, start, end - 1) + arr[end - 1] * \pow(2, end - 1 - start);
  }

  // Helper axiom: if all elements are 0, the value is 0.
  // Rule II.2: Helper axiom for recursive function.
  // This is not strictly necessary for the proof of this specific function,
  // but demonstrates the concept of helper axioms.
  // axiom binary_value_segment_zero:
  //   \forall int* arr, integer start, integer end;
  //     (\forall integer k; start <= k < end ==> arr[k] == 0) ==>
  //     binary_value_segment(arr, start, end) == 0;

  // The output array `binaryNum` must be large enough.
  // Let's assume MAX_BITS_FOR_INT is 32 for a standard int.
  // The function returns the number of bits used.
  // The bits are stored in reverse order (LSB at index 0).

  // `binaryNum` is an output parameter, so it's assigned.
  // The function assigns to `binaryNum` up to `result` elements.
  assigns binaryNum[0 .. result - 1];

  // Rule II.3: Ensures clause for boolean-like functions.
  // Not a boolean-like function, but the ensures clause specifies the output.
  // The function computes the binary representation of `n` and stores it
  // in `binaryNum` in reverse order.
  // The return value `result` is the number of bits required.
  ensures \forall integer k; 0 <= k < result ==> (binaryNum[k] == 0 || binaryNum[k] == 1);
  ensures result >= 0;
  // The value represented by the bits should be equal to n.
  ensures binary_value_segment(binaryNum, 0, result) == n;
  // If n is 0, result should be 1 and binaryNum[0] should be 0.
  ensures n == 0 ==> (result == 1 && binaryNum[0] == 0);
  // If n > 0, the most significant bit should be 1.
  ensures n > 0 ==> (result > 0 && binaryNum[result - 1] == 1);
*/
int decimal_to_binary(int n, int binaryNum[]) {
    int i = 0;
    // Rule II.4: Mandatory loop annotations.
    /*@
      loop invariant 0 <= i;
      loop invariant n_copy >= 0;
      // The value of the original n is preserved by the bits processed so far
      // plus the value of the remaining n_copy.
      loop invariant (\at(n, Pre) == binary_value_segment(binaryNum, 0, i) + n_copy * \pow(2, i));
      loop assigns i, n_copy, binaryNum[0 .. i - 1];
      // Rule II.4: Loop variant for termination.
      // The variant decreases as n_copy gets smaller.
      // log2(n_copy) is a good variant.
      // Or simply n_copy.
      loop variant n_copy;
    */
    for (int n_copy = n; n_copy > 0; n_copy /= 2) {
        // Store remainder in binary array
        binaryNum[i] = n_copy % 2;
        i++;
    }

    // Special case for n = 0
    if (n == 0) {
        binaryNum[0] = 0;
        return 1;
    }

    return i;
}
