// Task ID: 6
// Generation: 2

/*@
  // Axiomatic block for recursive logic (Rule II.1)
  axiomatic BitDiff {
    // Recursive logic function to count differing bits between two integers
    logic integer count_diff_bits_recursive(integer x, integer y, integer bit_pos) =
      if bit_pos < 0 then 0
      else
        (if ((x >> bit_pos) & 1) != ((y >> bit_pos) & 1) then 1 else 0) +
        count_diff_bits_recursive(x, y, bit_pos - 1);

    // Helper axiom: if bit_pos is negative, count is 0 (base case)
    axiom count_diff_bits_recursive_base:
      \forall integer x, y, bit_pos; bit_pos < 0 ==> count_diff_bits_recursive(x, y, bit_pos) == 0;

    // Helper axiom: for non-negative bit_pos, the recursive definition holds
    axiom count_diff_bits_recursive_step:
      \forall integer x, y, bit_pos; bit_pos >= 0 ==>
        count_diff_bits_recursive(x, y, bit_pos) ==
          (if ((x >> bit_pos) & 1) != ((y >> bit_pos) & 1) then 1 else 0) +
          count_diff_bits_recursive(x, y, bit_pos - 1);

    // Define a public logic function that uses the recursive one,
    // starting from the most significant bit (assuming 31 for int)
    logic integer count_diff_bits(integer x, integer y) =
      count_diff_bits_recursive(x, y, 31); // Assuming 32-bit integers
  }
*/

/*@
  // Rule II.5: No specific runtime errors expected for bitwise operations on int.
  // Rule I.2: `int` is used for boolean-like return.
  assigns \nothing;
  // Rule II.3: Ensures clause uses logical equivalence.
  ensures (count_diff_bits(num1, num2) == 1) <==> (\result == 1);
*/
int differ_by_one_bit(int num1, int num2) {
    int xor_result = num1 ^ num2;
    int count = 0;

    /*@
      loop invariant 0 <= count <= 32;
      loop invariant \forall integer k; 0 <= k < 32 - i ==> ((xor_result >> (31 - k)) & 1) == 0;
      loop invariant count == count_diff_bits_recursive(num1, num2, 31 - i); // Connects to axiomatic logic
      loop assigns i, count, xor_result; // xor_result changes implicitly due to right shift
      loop variant i;
    */
    for (int i = 0; i < 32; i++) { // Iterate through all 32 bits
        if ((xor_result & 1) == 1) {
            count++;
        }
        xor_result >>= 1;
    }

    return count == 1 ? 1 : 0; // Rule I.2: return 1 for true, 0 for false
}
