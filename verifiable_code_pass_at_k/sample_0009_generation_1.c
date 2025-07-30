// Task ID: 9
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Axiomatic block for string properties and rotations.
  // We need to define what a "rotation" means in terms of character arrays.
  // And then what it means for two strings to be equal (character by character).

  // A string is represented by a char array and its length.
  // We assume strings are null-terminated in C, but for ACSL, we use explicit length.

  axiomatic StringProperties {
    // Defines a character at a specific index in a string.
    logic char char_at(char *s, integer len, integer idx)
      reads s[0..len-1];

    axiom char_at_def{L}:
      \forall char *s, integer len, integer idx;
        0 <= idx < len ==> char_at(s, len, idx) == s[idx];

    // Defines a character at a specific index in a rotated string.
    // A string s of length len rotated by k positions means
    // s[i] moves to s[(i+k)%len].
    logic char rotated_char_at(char *s, integer len, integer k, integer idx)
      reads s[0..len-1];

    axiom rotated_char_at_def{L}:
      \forall char *s, integer len, integer k, integer idx;
        0 <= idx < len && 0 <= k < len ==>
          rotated_char_at(s, len, k, idx) == char_at(s, len, (idx + k) % len);

    // Defines string equality.
    predicate str_eq(char *s1, integer len1, char *s2, integer len2)
      reads s1[0..len1-1], s2[0..len2-1];

    axiom str_eq_def{L}:
      \forall char *s1, integer len1, char *s2, integer len2;
        str_eq(s1, len1, s2, len2) <==>
        (len1 == len2 && (\forall integer i; 0 <= i < len1 ==> char_at(s1, len1, i) == char_at(s2, len2, i)));

    // Defines that a string 's' is equal to its rotation by 'k' positions.
    predicate is_rotation_equal(char *s, integer len, integer k)
      reads s[0..len-1];

    axiom is_rotation_equal_def{L}:
      \forall char *s, integer len, integer k;
        0 <= k < len ==>
        is_rotation_equal(s, len, k) <==>
        (\forall integer i; 0 <= i < len ==> char_at(s, len, i) == rotated_char_at(s, len, k, i));

    // Helper axiom: if a string is equal to its rotation by k,
    // and also equal to its rotation by k', then it's also equal to its rotation by k + k'.
    // This isn't strictly necessary for the proof but can be a useful lemma for reasoning about rotations.
    // For this specific problem, we are looking for the *minimum* k.
    // So, this might be more complex than needed. The direct definition of is_rotation_equal is sufficient.

    // A string is always equal to its 0-rotation.
    axiom rotation_by_zero{L}:
      \forall char *s, integer len;
        len > 0 ==> is_rotation_equal(s, len, 0);
  }
*/

/*@
  requires len >= 1; // String must not be empty.
  requires \valid_read(s + (0..len-1)); // s must point to a readable array of 'len' chars.
  assigns \nothing;

  // The result is the minimum k (0 <= k < len) such that s is equal to its rotation by k.
  // Rule II.3: Use logical equivalence.
  ensures (\exists integer k; 0 <= k < len && is_rotation_equal(s, len, k) &&
           (\forall integer j; 0 <= j < k ==> !is_rotation_equal(s, len, j))) <==> (\result == k);
  // If no such k exists (which implies len=0, but we require len>=1),
  // the problem implies a solution always exists (at least k=0).
  // The problem asks for "minimum number of rotations".
  // If the string is "aaaa", k=1 is a rotation that yields the same string, but k=0 is the minimum.
  // So, the result will always be found.
  // For "abcabcabc", len=9, k=3 is the minimum.
*/
int min_rotations_for_same_string(char *s, int len) {
    if (len == 0) {
        return 0; // Edge case, though 'requires len >= 1' prevents this.
    }

    /*@
      loop invariant 0 <= k < len;
      // The current rotation 'k' is being tested.
      // For all 'prev_k' from 0 up to 'k-1', we have proved that 's' is NOT equal to its rotation by 'prev_k'.
      loop invariant \forall integer prev_k; 0 <= prev_k < k ==> !is_rotation_equal(s, len, prev_k);

      loop assigns k;
      loop variant len - k;
    */
    for (int k = 0; k < len; k++) {
        // Check if the string 's' is equal to its rotation by 'k' positions.
        // This means s[i] == s[(i+k)%len] for all i from 0 to len-1.
        int is_match = 1; // Rule I.2: Use int for boolean.

        /*@
          loop invariant 0 <= i <= len;
          // For all 'j' from 0 up to 'i-1', the characters match: s[j] == s[(j+k)%len].
          loop invariant \forall integer j; 0 <= j < i ==> char_at(s, len, j) == rotated_char_at(s, len, k, j);
          // If at any point 'is_match' became 0, it stays 0.
          loop invariant is_match == 1 ==> (\forall integer j; 0 <= j < i ==> char_at(s, len, j) == rotated_char_at(s, len, k, j));
          loop invariant is_match == 0 ==> (\exists integer j; 0 <= j < i && char_at(s, len, j) != rotated_char_at(s, len, k, j));

          loop assigns is_match, i;
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            // Rule II.5: No overflow for (i+k)%len as i, k, len are within int range.
            // The result of % is always non-negative for positive divisor.
            if (s[i] != s[(i + k) % len]) {
                is_match = 0;
                break;
            }
        }

        if (is_match == 1) {
            return k; // Found the minimum rotation.
        }
    }

    // This part should theoretically be unreachable if len >= 1,
    // as k=0 always results in a match (0 rotations).
    // However, for completeness, a return value is needed.
    return len; // Should not happen given the problem statement and k=0 case.
}
