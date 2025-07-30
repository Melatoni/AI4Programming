// Task ID: 9
// Generation: 0

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule II.5: Prevent potential overflow if len * len exceeds INT_MAX.
  // Max string length for a 32-bit int can be around 65535.
  // For practical purposes, a string length up to 10000 is usually safe for len*len.
  // Let's assume a reasonable maximum length for 's' to avoid overflow in len * len.
  // A string length of 46340 would cause len*len to exceed INT_MAX.
  // Given the problem context, let's assume 's' will not be excessively long.
  // For len * len to not overflow a 32-bit signed int, len must be <= 46340.
  // For a char array, a length of 10000 is already quite large.
  // Let's make an explicit requirement that the length is within a safe bound.
  requires \valid_read(s + (0..len-1));
  requires len >= 0;
  requires len <= 10000; // A reasonable upper bound to ensure len*len won't overflow for practical use.

  assigns \nothing;

  // Rule II.1: Define recursive logic for string equality and rotation.
  // Rule I.3: Array parameters decay to pointers.
  axiomatic StringOperations {
    logic int char_at_index(char *s, int len, int index)
      reads s[0..len-1];

    axiom char_at_index_def:
      \forall char *s, int len, int index;
        0 <= index < len ==> char_at_index(s, len, index) == s[index];

    // Checks if two strings are equal.
    logic int str_equal(char *s1, char *s2, int len)
      reads s1[0..len-1], s2[0..len-1];

    axiom str_equal_base:
      \forall char *s1, char *s2, int len;
        len == 0 ==> str_equal(s1, s2, len) == 1; // Empty strings are equal

    axiom str_equal_recursive:
      \forall char *s1, char *s2, int len;
        len > 0 ==> (str_equal(s1, s2, len) == (if char_at_index(s1, len, len-1) == char_at_index(s2, len, len-1) then str_equal(s1, s2, len-1) else 0));

    // Checks if the string 's' rotated by 'k' positions is equal to the original string 's'.
    // A rotation by 'k' means the character at original index 'i' moves to index '(i+k) % len'.
    logic int is_rotated_equal(char *s, int len, int k)
      reads s[0..len-1];

    axiom is_rotated_equal_base_len0:
      \forall char *s, int k;
        0 == 0 ==> is_rotated_equal(s, 0, k) == 1; // Empty string is always equal to itself after any rotation

    axiom is_rotated_equal_base_k0:
      \forall char *s, int len;
        0 == 0 ==> is_rotated_equal(s, len, 0) == 1; // 0 rotation means it's always equal

    axiom is_rotated_equal_recursive:
      \forall char *s, int len, int k, int i;
        0 <= i < len ==> (char_at_index(s, len, i) == char_at_index(s, len, (i + k) % len));

    // Helper axiom: if is_rotated_equal holds for a specific k, it means all characters match their rotated counterparts.
    // This axiom helps the prover connect the loop iteration logic to the overall property.
    // Rule II.2: CRITICAL - Helper Axioms
    axiom is_rotated_equal_character_match:
      \forall char *s, int len, int k;
        is_rotated_equal(s, len, k) == 1 ==>
        (\forall integer i; 0 <= i < len ==> char_at_index(s, len, i) == char_at_index(s, len, (i + k) % len));

    axiom is_rotated_equal_character_match_rev:
      \forall char *s, int len, int k;
        (\forall integer i; 0 <= i < len ==> char_at_index(s, len, i) == char_at_index(s, len, (i + k) % len)) ==>
        is_rotated_equal(s, len, k) == 1;
  }

  // Rule II.3: Use the logical equivalence operator <==>.
  ensures \result >= 0;
  ensures \result <= len;
  ensures (\exists integer k; 0 <= k < len && is_rotated_equal(s, len, k) == 1 &&
           (\forall integer j; 0 <= j < k ==> is_rotated_equal(s, len, j) == 0)) <==> (\result > 0);
  ensures (\result == 0) <==> (len == 0);
  ensures (\result > 0) ==> is_rotated_equal(s, len, \result) == 1;
  ensures (\result > 0) ==> (\forall integer j; 0 <= j < \result ==> is_rotated_equal(s, len, j) == 0);
*/
int min_rotations_to_same_string(char *s, int len) {
    if (len == 0) {
        return 0;
    }

    // Rule II.4: Mandatory loop annotations.
    /*@
      loop invariant 0 <= k <= len;
      loop invariant \forall integer j; 0 <= j < k ==> is_rotated_equal(s, len, j) == 0;
      loop assigns k, i; // 'i' is assigned within the inner loop
      loop variant len - k;
    */
    for (int k = 1; k < len; k++) {
        int is_equal = 1; // Rule I.2: Use int for booleans.

        /*@
          loop invariant 0 <= i <= len;
          loop invariant is_equal == 1 ==> \forall integer p; 0 <= p < i ==> s[p] == s[(p + k) % len];
          loop assigns i, is_equal;
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            // Rule II.5: Prevent RTE - ensure (i + k) % len is valid.
            // (i + k) is guaranteed to be non-negative. % len will also be non-negative.
            // len is guaranteed to be > 0 here because of the initial check.
            // s[i] and s[(i + k) % len] are valid because 0 <= i < len and 0 <= (i + k) % len < len.
            if (s[i] != s[(i + k) % len]) {
                is_equal = 0;
                break;
            }
        }

        if (is_equal == 1) {
            return k;
        }
    }

    // If no rotation (other than 0) makes the string equal,
    // it means only len rotations (back to original) makes it equal.
    // This implies the string consists of all the same characters, or it's a unique string.
    // E.g., "aaaa" -> 1 rotation. "abcde" -> 5 rotations.
    // The loop finds the smallest k > 0. If no such k is found, it means the string
    // only matches itself at 0 rotation (which is represented by 'len' rotations).
    return len;
}
