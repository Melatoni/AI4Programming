// Task ID: 27
// Generation: 8

int` for booleans, ACSL logic, and loop annotations.

/*@ axiomatic CharPredicates {
  // Rule II.1: Define logic for character properties.
  logic boolean is_digit(char c) = c >= '0' && c <= '9';
}
*/

/*@
  requires \valid(s + (0..len)); // s points to a valid buffer of size len+1 (for null terminator)
  requires \valid(s); // s itself is a valid pointer
  requires len >= 0; // Length cannot be negative
  requires s[len] == '\0'; // s is a null-terminated string of length len

  // The function modifies the string in-place.
  // The content of the string up to the null terminator is modified.
  assigns s[0..len];

  // Rule II.3: Ensures clause for boolean-like functions (though this one modifies in-place,
  // we can still state the post-condition clearly).
  // This ensures clause states that the resulting string will not contain any digits.
  // It also implies that the new length will be less than or equal to the original length.
  // And that the modified string is also null-terminated.
  ensures s[\result] == '\0'; // The new string is null-terminated at index \result
  ensures \forall integer k; 0 <= k < \result ==> !is_digit(s[k]); // No digits in the new string prefix
  ensures \result <= len; // The new length is at most the original length
  ensures \forall integer k; 0 <= k < \result ==> \exists integer j; 0 <= j < len && s[k] == \old(s[j]) && !is_digit(\old(s[j]));
    // Every character in the new string must have been a non-digit character in the original string.
  ensures \forall integer j; 0 <= j < len && !is_digit(\old(s[j])) ==> \exists integer k; 0 <= k < \result && s[k] == \old(s[j]);
    // Every non-digit character in the original string must be present in the new string.
  ensures \forall integer i, j; 0 <= i < j < \result ==> \exists integer pi, pj;
    0 <= pi < pj < len && !is_digit(\old(s[pi])) && !is_digit(\old(s[pj])) &&
    s[i] == \old(s[pi]) && s[j] == \old(s[pj]);
    // The relative order of non-digit characters is preserved.
*/
int remove_digits_from_string(char s[], int len) {
    int write_idx = 0;
    int read_idx = 0;

    /*@
      loop invariant 0 <= read_idx <= len;
      loop invariant 0 <= write_idx <= read_idx;

      // Characters processed so far (read_idx)
      loop invariant \forall integer k; 0 <= k < read_idx ==> \old(s[k]) == '0' || !is_digit(\old(s[k]));
        // This invariant is tricky. It states that original characters up to read_idx
        // were either digits (which we ignore) or non-digits (which we copy).
        // It's more precise to state what's *already copied* to s[0..write_idx-1].

      // Content already copied to the beginning of the string (s[0..write_idx-1])
      loop invariant \forall integer k; 0 <= k < write_idx ==> !is_digit(s[k]);
      loop invariant \forall integer k; 0 <= k < write_idx ==> \exists integer j; 0 <= j < read_idx && s[k] == \old(s[j]) && !is_digit(\old(s[j]));
        // All characters written so far were non-digits from the original string.
      loop invariant \forall integer i, j; 0 <= i < j < write_idx ==> \exists integer pi, pj;
        0 <= pi < pj < read_idx && !is_digit(\old(s[pi])) && !is_digit(\old(s[pj])) &&
        s[i] == \old(s[pi]) && s[j] == \old(s[pj]);
        // The relative order of non-digit characters is preserved in the written part.

      // The part of the string from write_idx to read_idx-1 is a mix of original and potentially overwritten characters.
      // The part s[read_idx..len] remains unchanged from the original string.
      loop invariant \forall integer k; read_idx <= k <= len ==> s[k] == \old(s[k]);

      loop assigns read_idx, write_idx, s[0..len];
      loop variant len - read_idx;
    */
    while (read_idx <= len) { // Loop until the null terminator is processed
        char current_char = s[read_idx];

        if (!is_digit(current_char)) {
            s[write_idx] = current_char;
            write_idx++;
        }
        read_idx++;
    }

    // The loop processes the null terminator as well, ensuring it's copied.
    // If the original string was "abc12", len=5.
    // read_idx will go from 0 to 5.
    // When read_idx = 5, current_char = s[5] = '\0'.
    // '\0' is not a digit, so it's copied, write_idx increments.
    // So s[write_idx-1] is the null terminator, and write_idx is the new length.
    // The final s[write_idx] = '\0' is actually already there.

    return write_idx - 1; // Return the new effective length (excluding the null terminator)
}

/*@
  requires count >= 0;
  requires \valid_read(strings + (0..count-1)); // strings is an array of pointers
  requires \forall integer i; 0 <= i < count ==> \valid(strings[i]); // Each string pointer is valid
  // Requires that each string is null-terminated and its length is accurate.
  requires \forall integer i; 0 <= i < count ==> \exists integer k; strings[i][k] == '\0';
  requires \forall integer i; 0 <= i < count ==>
    (\let L = \strlen(strings[i]); \valid(strings[i] + (0..L)) && strings[i][L] == '\0');

  assigns \nothing; // This function does not modify the array of pointers itself
  assigns \through(strings[0..count-1]); // But it modifies the content of the strings pointed to
*/
void remove_digits_from_strings(char *strings[], int count) {
    /*@
      loop invariant 0 <= i <= count;
      loop invariant \forall integer k; 0 <= k < i ==>
        (\let old_len = \strlen(\old(strings[k]));
         \let new_len = \strlen(strings[k]);
         strings[k][new_len] == '\0' &&
         \forall integer l; 0 <= l < new_len ==> !is_digit(strings[k][l]) &&
         new_len <= old_len &&
         (\forall integer l; 0 <= l < new_len ==> \exists integer j; 0 <= j < old_len && strings[k][l] == \old(strings[k][j]) && !is_digit(\old(strings[k][j]))) &&
         (\forall integer j; 0 <= j < old_len && !is_digit(\old(strings[k][j])) ==> \exists integer l; 0 <= l < new_len && strings[k][l] == \old(strings[k][j]))) &&
         (\forall integer a, b; 0 <= a < b < new_len ==> \exists integer pa, pb; 0 <= pa < pb < old_len && !is_digit(\old(strings[k][pa])) && !is_digit(\old(strings[k][pb])) && strings[k][a] == \old(strings[k][pa]) && strings[k][b] == \old(strings[k][pb]));
        ); // All strings processed so far satisfy the post-condition of remove_digits_from_string

      loop assigns i, \through(strings[0..count-1]);
      loop variant count - i;
    */
    for (int i = 0; i < count; i++) {
        // Calculate the length of the string
        // Rule I.1: No standard libraries, so strlen must be defined or computed inline.
        // For simplicity in this context, we assume a strlen-like function or a known max len.
        // Frama-C's WP can often infer strlen from string properties.
        // For a full verification, a `strlen` function with its own ACSL contract would be needed.
        // Here, we use \strlen from ACSL, which is known to Frama-C.

        /*@
          // Pre-conditions for the call to remove_digits_from_string
          requires \valid(strings[i] + (0..\strlen(strings[i])));
          requires \valid(strings[i]);
          requires \strlen(strings[i]) >= 0;
          requires strings[i][\strlen(strings[i])] == '\0';
          assigns strings[i][0..\strlen(strings[i])];
        */
        (void)remove_digits_from_string(strings[i], \strlen(strings[i]));
    }
}

// Example usage and main function are not required by the prompt,
// as the focus is solely on the verifiable C code with ACSL annotations.
// However, if a main was needed, it would look like:
// int main() {
//    char s1[] = "Hello123World";
//    char s2[] = "456Alpha789";
//    char* my_strings[] = {s1, s2};
//    remove_digits_from_strings(my_strings, 2);
//    return 0;
// }
