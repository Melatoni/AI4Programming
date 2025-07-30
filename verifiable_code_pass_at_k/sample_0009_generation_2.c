// Task ID: 9
// Generation: 2

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule II.5: Prevent potential overflow in string length calculations or indexing.
  // The maximum length for a string that can be safely handled by int.
  // This is a heuristic; more precise bounds might involve the maximum value of int.
  requires 0 <= len <= 20000; // Assuming reasonable string length for an int type.
*/
int get_min_rotations(char *s, int len);

/*@
  // Rule II.1: Define recursive logic for string equality.
  axiomatic StringEquality {
    logic boolean string_eq_at(char *s1, int start1, char *s2, int start2, int len);

    axiom string_eq_at_base:
      \forall char *s1, char *s2, integer start1, start2, len;
        len == 0 ==> string_eq_at(s1, start1, s2, start2, len);

    axiom string_eq_at_recursive:
      \forall char *s1, char *s2, integer start1, start2, len;
        len > 0 ==> (string_eq_at(s1, start1, s2, start2, len) <==>
                      s1[start1] == s2[start2] && string_eq_at(s1, start1 + 1, s2, start2 + 1, len - 1));
  }
*/

/*@
  // Rule II.1: Define recursive logic for checking if a rotation matches the original.
  axiomatic RotationMatchesOriginal {
    logic boolean is_rotated_match(char *s, int len, int rotation_idx);

    // If rotation_idx is 0, it's always a match (original string).
    axiom is_rotated_match_base_0:
      \forall char *s, integer len;
        is_rotated_match(s, len, 0);

    // Recursive definition for a general rotation_idx.
    // The rotated string is s[rotation_idx...len-1] + s[0...rotation_idx-1].
    // We need to compare this concatenation with the original string s[0...len-1].
    // This requires comparing two segments:
    // 1. s[rotation_idx .. len-1] with s[0 .. len-1-rotation_idx]
    // 2. s[0 .. rotation_idx-1] with s[len-rotation_idx .. len-1]
    axiom is_rotated_match_recursive:
      \forall char *s, integer len, integer rotation_idx;
        0 < rotation_idx <= len ==>
        (is_rotated_match(s, len, rotation_idx) <==>
           string_eq_at(s, rotation_idx, s, 0, len - rotation_idx) &&
           string_eq_at(s, 0, s, len - rotation_idx, rotation_idx));
  }
*/


/*@
  requires len >= 0;
  // Rule II.5: Prevent potential overflow if len is large.
  // Max len for char array, assuming it's within int limits.
  requires len <= 20000;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like functions.
  // The result is 'k' if 'k' is the smallest positive integer such that
  // rotating the string by 'k' positions results in the original string.
  // If no such positive 'k' exists (e.g., all characters are the same),
  // the result is 'len'.
  ensures (\exists integer k; 1 <= k <= len && is_rotated_match(s, len, k) &&
           (\forall integer j; 1 <= j < k ==> !is_rotated_match(s, len, j))) <==> (result == k);
  ensures (\forall integer k; 1 <= k <= len ==> !is_rotated_match(s, len, k)) <==> (result == len);
*/
int get_min_rotations(char *s, int len) {
    if (len == 0) {
        return 0;
    }

    /*@
      loop invariant 0 <= i <= len;
      loop invariant 0 <= k <= len;
      loop invariant k == (\min integer r; 1 <= r < i && is_rotated_match(s, len, r) ? r : len);
      // The `k` variable stores the minimum rotation found so far.
      // If no rotation has been found, `k` remains `len`.
      // This invariant captures that `k` is the smallest rotation that matches,
      // among rotations from 1 to `i-1`.
      // If no such rotation exists up to `i-1`, `k` should ideally be `len`.

      loop assigns i, k;
      loop variant len - i;
    */
    for (int i = 1; i < len; i++) {
        // Check if s[i...len-1] + s[0...i-1] == s[0...len-1]
        // This is equivalent to checking if the string rotated by 'i' positions
        // is equal to the original string.
        /*@
          assert \forall integer idx; 0 <= idx < len - i ==> s[idx + i] == s[idx];
          assert \forall integer idx; 0 <= idx < i ==> s[idx] == s[len - i + idx];
        */
        if (is_rotated_match(s, len, i)) {
            return i;
        }
    }

    // If no rotation (other than 0) results in the original string,
    // it means all characters are the same (e.g., "aaaa"), or it's a unique string.
    // In this case, 'len' rotations are required to get back to the original.
    // This also covers cases like "abc" where 3 rotations are needed.
    return len;
}
