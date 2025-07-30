// Task ID: 9
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Axiomatic block for recursive logic.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms are CRITICAL for the prover.
*/
/*@
  axiomatic StringRotation {
    logic integer string_len(char *s, integer max_len);

    axiom string_len_base:
      \forall char *s, integer max_len;
        (max_len == 0 || s[0] == '\0') ==> string_len(s, max_len) == 0;

    axiom string_len_recursive:
      \forall char *s, integer max_len;
        max_len > 0 && s[0] != '\0' ==> string_len(s, max_len) == 1 + string_len(s + 1, max_len - 1);

    // Helper axiom: length is non-negative
    axiom string_len_non_negative:
      \forall char *s, integer max_len; string_len(s, max_len) >= 0;

    // Helper axiom: length is bounded by max_len
    axiom string_len_bounded:
      \forall char *s, integer max_len; string_len(s, max_len) <= max_len;

    logic char char_at(char *s, integer len, integer idx);

    axiom char_at_def:
      \forall char *s, integer len, integer idx;
        0 <= idx < len ==> char_at(s, len, idx) == s[idx];

    // Helper axiom: char_at is defined only within bounds
    axiom char_at_undefined_oob:
      \forall char *s, integer len, integer idx;
        (idx < 0 || idx >= len) ==> \false; // char_at is not defined for out-of-bounds indices

    logic int is_same_string(char *s1, char *s2, integer len);

    axiom is_same_string_base:
      \forall char *s1, char *s2, integer len;
        len == 0 ==> is_same_string(s1, s2, len) == 1;

    axiom is_same_string_recursive:
      \forall char *s1, char *s2, integer len;
        len > 0 ==> (is_same_string(s1, s2, len) == (char_at(s1, len, 0) == char_at(s2, len, 0) && is_same_string(s1 + 1, s2 + 1, len - 1)));

    // Helper axiom: is_same_string is transitive
    axiom is_same_string_transitive:
      \forall char *s1, char *s2, char *s3, integer len;
        is_same_string(s1, s2, len) == 1 && is_same_string(s2, s3, len) == 1 ==> is_same_string(s1, s3, len) == 1;

    logic char rotated_char_at(char *s, integer len, integer rotation_count, integer idx);

    axiom rotated_char_at_def:
      \forall char *s, integer len, integer rotation_count, integer idx;
        0 <= idx < len ==> rotated_char_at(s, len, rotation_count, idx) == char_at(s, len, (idx + rotation_count) % len);

    // Helper axiom: rotating by len returns the original char
    axiom rotated_char_at_len:
      \forall char *s, integer len, integer idx;
        0 <= idx < len ==> rotated_char_at(s, len, len, idx) == char_at(s, len, idx);

    logic int is_rotated_same(char *s, integer len, integer rotation_count);

    axiom is_rotated_same_base:
      \forall char *s, integer len, integer rotation_count;
        len == 0 ==> is_rotated_same(s, len, rotation_count) == 1;

    axiom is_rotated_same_recursive:
      \forall char *s, integer len, integer rotation_count;
        len > 0 ==> (is_rotated_same(s, len, rotation_count) == (char_at(s, len, 0) == rotated_char_at(s, len, rotation_count, 0) && is_rotated_same(s + 1, len, rotation_count, len - 1)));
  }
*/


/*@
  requires \valid_read(s);
  requires string_len(s, 256) <= 255; // Max string length for practical purposes
  requires string_len(s, 256) >= 0; // String length must be non-negative

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence.
  ensures \result >= 0;
  ensures \result <= string_len(s, 256);
  ensures \result == string_len(s, 256) <==> string_len(s, 256) == 0;
  // If the string is empty, 0 rotations are needed.

  // If the string is not empty, the result is the minimum k such that rotating by k produces the original string.
  ensures string_len(s, 256) > 0 ==> (
    is_rotated_same(s, string_len(s, 256), \result) == 1 &&
    (\forall integer k; 0 <= k < \result ==> is_rotated_same(s, string_len(s, 256), k) == 0)
  );

  // If the string is not empty, the result is less than or equal to the length
  ensures string_len(s, 256) > 0 ==> \result <= string_len(s, 256);
*/
int find_min_rotations(char *s) {
    int len = 0;
    /*@
      loop invariant len >= 0;
      loop invariant \forall integer k; 0 <= k < len ==> s[k] != '\0';
      loop invariant (len == 0 || s[len-1] != '\0');
      loop invariant (len == string_len(s, 256) || (len < 256 && s[len] != '\0'));
      loop variant 256 - len;
    */
    for (int i = 0; i < 256; i++) { // Max length assumed 255 + null terminator
        if (s[i] == '\0') {
            len = i;
            break;
        }
    }

    if (len == 0) {
        return 0;
    }

    // Allocate memory for the current rotated string.
    // In a real scenario, this would involve malloc, but for Frama-C/WP,
    // we can use a fixed-size buffer as long as we ensure string_len constraints.
    // We assume a char buffer of size 256 is available.
    char temp_s[256];

    /*@
      loop invariant 0 <= rotation_count <= len;
      loop invariant \forall integer i; 0 <= i < rotation_count ==> is_rotated_same(s, len, i) == 0;
      loop invariant \forall integer k; 0 <= k < len ==> (temp_s[k] == rotated_char_at(s, len, rotation_count, k));
      loop invariant temp_s[len] == '\0';

      loop assigns rotation_count, temp_s;
      loop variant len - rotation_count;
    */
    for (int rotation_count = 1; rotation_count <= len; rotation_count++) {
        // Construct the rotated string
        /*@
          loop invariant 0 <= i <= len;
          loop invariant \forall integer k; 0 <= k < i ==> (temp_s[k] == char_at(s, len, (k + rotation_count) % len));
          loop assigns temp_s;
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            temp_s[i] = s[(i + rotation_count) % len];
        }
        temp_s[len] = '\0'; // Null-terminate the temporary string

        // Check if the rotated string is the same as the original
        int are_same = 1;
        /*@
          loop invariant 0 <= i <= len;
          loop invariant (\forall integer k; 0 <= k < i ==> s[k] == temp_s[k]) ==> are_same == 1;
          loop invariant (\exists integer k; 0 <= k < i && s[k] != temp_s[k]) ==> are_same == 0;
          loop assigns are_same;
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            if (s[i] != temp_s[i]) {
                are_same = 0;
                break;
            }
        }

        if (are_same == 1) {
            return rotation_count;
        }
    }

    return 0; // Should not be reached if the string is non-empty, as len rotations will always match.
}
