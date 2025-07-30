// Task ID: 9
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define a recursive logic function for string equality after rotation.
  // This is crucial for verifying string properties without stdlib.
  axiomatic StringRotation {
    logic int char_at(char *s, int len, int index);

    axiom char_at_def:
      \forall char *s, int len, int index;
        0 <= index < len ==> char_at(s, len, index) == s[index];

    // Checks if string s1 (length len) is equal to string s2 (length len) starting from index offset.
    // This function will be used to check if the rotated string is equal to the original.
    logic int is_equal_rotated_at(char *s1, char *s2, int len, int offset, int k);

    axiom is_equal_rotated_at_base:
      \forall char *s1, char *s2, int len, int offset;
        k == 0 ==> (is_equal_rotated_at(s1, s2, len, offset, 0) == 1 <==> char_at(s1, len, 0) == char_at(s2, len, (0 + offset) % len));

    axiom is_equal_rotated_at_rec:
      \forall char *s1, char *s2, int len, int offset, int k;
        k > 0 && k < len ==> (is_equal_rotated_at(s1, s2, len, offset, k) == 1 <==> (char_at(s1, len, k) == char_at(s2, len, (k + offset) % len) && is_equal_rotated_at(s1, s2, len, offset, k-1) == 1));

    // Helper axiom: If a string is equal to its rotation at offset i, then it is equal for all indices.
    // This helps the prover understand the recursive definition.
    axiom is_equal_rotated_at_property:
      \forall char *s1, char *s2, int len, int offset;
        (is_equal_rotated_at(s1, s2, len, offset, len - 1) == 1) <==>
        (\forall integer k; 0 <= k < len ==> char_at(s1, len, k) == char_at(s2, len, (k + offset) % len));
  }
*/

/*@
  requires \valid_read_string(s);
  requires len > 0;
  requires \strlen(s) == len; // Ensure the provided length matches the actual string length.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The result is the minimum k (1 <= k <= len) such that rotating s by k positions results in s.
  ensures 1 <= \result <= len;
  ensures is_equal_rotated_at(s, s, len, \result, len - 1) == 1;
  ensures \forall integer k; 1 <= k < \result ==> is_equal_rotated_at(s, s, len, k, len - 1) == 0;
*/
int min_rotations_for_same_string(char *s, int len) {
    /*@
      loop invariant 1 <= k <= len;
      // The current k is the smallest rotation count found so far that makes the string equal to itself.
      // If we haven't found one yet, then no k < current_k satisfies the condition.
      loop invariant (\forall integer i; 1 <= i < k ==> is_equal_rotated_at(s, s, len, i, len - 1) == 0);
      loop assigns k;
      // Rule II.4: A loop variant is mandatory for termination.
      loop variant len - k;
    */
    for (int k = 1; k <= len; k++) {
        // Check if rotating the string by 'k' positions results in the original string.
        // Rule II.1: Using the recursive logic function.
        if (is_equal_rotated_at(s, s, len, k, len - 1) == 1) {
            return k; // Found the minimum rotation.
        }
    }
    return len; // Should not be reached if len > 0, as rotating by 'len' always returns the same string.
                // Added for completeness/safety, but the ensures clause implies it will find a k <= len.
}
