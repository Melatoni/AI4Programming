// Task ID: 41
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define a recursive logic function for properties over sequences.
  // This axiomatic block defines the properties of the filter operation.
  axiomatic FilterEven {
    logic int is_even(int x) = (x % 2 == 0);

    // Filtered array definition: elements should be even and in order.
    logic int is_filtered_correctly(int* src, int src_len, int* dest, int dest_len) reads src[0..src_len-1], dest[0..dest_len-1];

    // Base case: An empty destination array is correctly filtered from an empty source array.
    axiom is_filtered_correctly_base_empty:
      \forall int* src, int* dest;
        is_filtered_correctly(src, 0, dest, 0);

    // Recursive case for when the source array is not empty.
    axiom is_filtered_correctly_recursive:
      \forall int* src, int src_len, int* dest, int dest_len;
        src_len > 0 ==> (
          is_filtered_correctly(src, src_len, dest, dest_len) <==> (
            // If the first element of src is even, it must be the first element of dest,
            // and the rest of dest must be correctly filtered from the rest of src.
            (is_even(src[0]) && dest_len > 0 && dest[0] == src[0] &&
             is_filtered_correctly(src + 1, src_len - 1, dest + 1, dest_len - 1))
            ||
            // If the first element of src is odd, it must not be in dest,
            // and dest must be correctly filtered from the rest of src.
            (!is_even(src[0]) &&
             is_filtered_correctly(src + 1, src_len - 1, dest, dest_len))
          )
        );

    // Helper axiom (Rule II.2): The length of the filtered array must be less than or equal to the source array.
    axiom filtered_length_le_src_length:
      \forall int* src, int src_len, int* dest, int dest_len;
        is_filtered_correctly(src, src_len, dest, dest_len) ==> dest_len <= src_len;

    // Helper axiom (Rule II.2): All elements in the filtered array must be even.
    axiom filtered_elements_are_even:
      \forall int* src, int src_len, int* dest, int dest_len;
        is_filtered_correctly(src, src_len, dest, dest_len) ==>
          \forall integer i; 0 <= i < dest_len ==> is_even(dest[i]);
  }
*/

/*@
  requires \valid_read(src + (0..src_len-1));
  requires \valid_write(dest + (0..src_len-1)); // dest must be large enough to hold all elements from src in worst case
  requires src_len >= 0;

  assigns dest[0..src_len-1];

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The function returns the number of even elements filtered.
  ensures \result >= 0 && \result <= src_len;
  ensures is_filtered_correctly(src, src_len, dest, \result);
*/
int filter_even(int* src, int src_len, int* dest) {
    int count = 0;
    /*@
      loop invariant 0 <= i <= src_len;
      loop invariant 0 <= count <= i;
      // Rule II.4: Loop invariant for the filtered prefix of dest.
      loop invariant is_filtered_correctly(src, i, dest, count);
      loop assigns count, dest[0..i-1]; // Correct assignment for dest based on count and i
      loop variant src_len - i;
    */
    for (int i = 0; i < src_len; i++) {
        // Equivalent to a lambda function (x) => x % 2 == 0
        if (src[i] % 2 == 0) {
            dest[count] = src[i];
            count++;
        }
    }
    return count;
}
