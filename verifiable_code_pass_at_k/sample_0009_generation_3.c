// Task ID: 9
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: int for booleans.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  axiomatic StringRotation {
    logic int is_equal_rotated_at(char *s1, char *s2, int len, int rotation_idx);

    axiom is_equal_rotated_at_base_case:
      \forall char *s1, *s2, int len, rotation_idx;
        len == 0 ==> is_equal_rotated_at(s1, s2, len, rotation_idx) == 1;

    axiom is_equal_rotated_at_recursive_case:
      \forall char *s1, *s2, int len, rotation_idx;
        len > 0 ==>
          (is_equal_rotated_at(s1, s2, len, rotation_idx) ==
           ((s1[len - 1] == s2[(len - 1 + rotation_idx) % len]) &&
            is_equal_rotated_at(s1, s2, len - 1, rotation_idx)));

    // Helper axiom: if strings are equal after rotation, they must have the same length.
    // This is implicitly handled by passing 'len' as an argument, but good to think about.

    // Helper axiom: If is_equal_at(s1, s2, len, rotation_idx) is true,
    // then s1[i] == s2[(i + rotation_idx) % len] for all 0 <= i < len.
    // This is crucial for the correctness proof.
    axiom is_equal_rotated_at_property:
      \forall char *s1, *s2, int len, rotation_idx;
        is_equal_rotated_at(s1, s2, len, rotation_idx) == 1 ==>
          \forall integer i; 0 <= i < len ==> s1[i] == s2[(i + rotation_idx) % len];
  }
*/

/*@
  requires \valid_read_string(s);
  requires \strlen(s) >= 0;
  // Rule II.5: Prevent potential overflow if len is very large, though unlikely for string length.
  // Consider max string length that fits in int.
  // No specific overflow for this problem's logic, but good practice.

  assigns \nothing;

  // Rule II.3: Ensures clause using logical equivalence.
  ensures \result >= 0;
  ensures \result <= \strlen(s);
  ensures (\result == 0 && \strlen(s) == 0) || // Empty string case
          (\result == \strlen(s) && \strlen(s) > 0 && // No rotation makes it equal OR
           \forall integer k; 0 <= k < \strlen(s) && k != \result ==>
             is_equal_rotated_at(s, s, \strlen(s), k) == 0) || // No other rotation makes it equal
          (\result > 0 && \result < \strlen(s) && // Found a minimal rotation
           is_equal_rotated_at(s, s, \strlen(s), \result) == 1 &&
           // Rule III.2: No parentheses around if-then-else
           \forall integer k; 0 <= k < \result ==> is_equal_rotated_at(s, s, \strlen(s), k) == 0);
*/
int min_rotations_for_same_string(char *s) {
    int len = 0;
    /*@
      loop invariant len >= 0;
      loop invariant \valid_read_string(s);
      loop invariant \forall integer k; 0 <= k < len ==> s[k] != '\0';
      loop assigns len;
      loop variant \at(\strlen(s), Pre) - len;
    */
    while (s[len] != '\0') {
        len++;
    }

    if (len == 0) {
        return 0;
    }

    int k = 1; // Current rotation candidate
    int result = len; // Initialize with maximum possible rotations (no match)

    /*@
      loop invariant 0 <= k && k <= len;
      loop invariant 0 <= result && result <= len;
      loop invariant \forall integer i; 0 <= i < k ==>
        // If a match was found at 'i', then result <= i.
        // If no match was found for any j < k, then result is still len or the first match.
        (is_equal_rotated_at(s, s, len, i) == 1 ==> result <= i);
      loop invariant (result < len) ==>
        (is_equal_rotated_at(s, s, len, result) == 1);
      loop invariant (result == len) ==>
        (\forall integer i; 0 <= i < k ==> is_equal_rotated_at(s, s, len, i) == 0);

      loop assigns k, result;
      loop variant len - k;
    */
    while (k < len) {
        /*@
          // Rule III.1: No C-style ternary in ACSL.
          // Rule III.2: No parentheses around if-then-else.
          // Rule III.3: Correct range syntax.
          // Rule II.2: Helper axiom for loop body correctness.
          // If is_equal_rotated_at(s, s, len, k) is true, it implies that
          // s is equal to its rotation by k.
          // We need to prove this equivalence for the WP.
          // (is_equal_rotated_at(s, s, len, k) == 1) <==>
          //   (\forall integer i; 0 <= i < len ==> s[i] == s[(i + k) % len])
        */
        int is_match = 1; // Assume match
        /*@
          loop invariant 0 <= i && i <= len;
          loop invariant is_match == 1 ==> \forall integer j; 0 <= j < i ==> s[j] == s[(j + k) % len];
          loop invariant is_match == 0 ==> \exists integer j; 0 <= j < i && s[j] != s[(j + k) % len];
          loop assigns i, is_match;
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            if (s[i] != s[(i + k) % len]) {
                is_match = 0;
                break;
            }
        }

        if (is_match == 1) {
            result = k; // Found the first rotation that results in the same string
            break;     // Since we are looking for the minimum, we can stop
        }
        k++;
    }

    return result;
}
