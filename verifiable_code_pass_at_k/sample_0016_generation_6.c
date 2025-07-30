// Task ID: 16
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic CharProperties {
    logic boolean is_lowercase_letter(char c) = (c >= 'a' && c <= 'z');
  }
*/

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like functions.
  // This function checks if a character at a given index is a lowercase letter.
  ensures (\result == 1) <==> is_lowercase_letter(s[index]);
*/
int is_char_lowercase_letter(char *s, int len, int index) {
    if (index < 0 || index >= len) {
        return 0; // Out of bounds, not a letter.
    }
    if (s[index] >= 'a' && s[index] <= 'z') {
        return 1;
    }
    return 0;
}

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;
  requires start_idx >= 0 && start_idx < len;

  assigns \nothing;

  // Rule II.1: Recursive logic for complexity.
  // This logic function checks if a segment of the string from start_idx to end_idx-1
  // consists entirely of lowercase letters.
  logic boolean is_lowercase_segment(char *s, int len, int start_idx, int end_idx) =
    (start_idx >= end_idx) ||
    (is_char_lowercase_letter(s, len, start_idx) && is_lowercase_segment(s, len, start_idx + 1, end_idx));

  // Rule II.2: Helper axioms for recursive logic.
  // Axiom 1: Base case for empty segment.
  axiom is_lowercase_segment_empty:
    \forall char *s, int len, int start_idx, int end_idx;
      start_idx >= end_idx ==> is_lowercase_segment(s, len, start_idx, end_idx) == \true;

  // Axiom 2: Recursive step.
  axiom is_lowercase_segment_recursive:
    \forall char *s, int len, int start_idx, int end_idx;
      start_idx < end_idx ==>
      is_lowercase_segment(s, len, start_idx, end_idx) ==
      (is_char_lowercase_letter(s, len, start_idx) && is_lowercase_segment(s, len, start_idx + 1, end_idx));
*/

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;
  requires start_idx >= 0 && start_idx < len;

  assigns \nothing;

  // Checks if the character at start_idx is an underscore.
  ensures (\result == 1) <==> (s[start_idx] == '_');
*/
int is_char_underscore(char *s, int len, int start_idx) {
    if (start_idx < 0 || start_idx >= len) {
        return 0; // Out of bounds, not an underscore.
    }
    if (s[start_idx] == '_') {
        return 1;
    }
    return 0;
}

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // Rule II.1: The function returns 1 if there exists a sequence of the form (lowercase_letters)_ (lowercase_letters)
  // Rule II.5: Implied by loop invariants and bounds checks.
  ensures (\exists integer i, j, k;
              0 <= i && i < j && j < k && k <= len &&
              is_lowercase_segment(s, len, i, j) &&
              is_char_underscore(s, len, j) && // underscore at index j
              is_lowercase_segment(s, len, j + 1, k)
          ) <==> (\result == 1);
*/
int find_sequence(char *s, int len) {
    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant \forall integer x, y, z;
        0 <= x && x < y && y < z && z <= i ==>
        !(is_lowercase_segment(s, len, x, y) && is_char_underscore(s, len, y) && is_lowercase_segment(s, len, y + 1, z));
      loop assigns i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Iterate through all possible start positions of the first segment
        // i will be the start of the first lowercase segment

        if (is_char_lowercase_letter(s, len, i) == 1) {
            /*@
              loop invariant i <= j && j <= len;
              loop invariant is_lowercase_segment(s, len, i, j);
              loop invariant \forall integer y, z;
                i <= y && y < z && z <= j &&
                !(is_char_underscore(s, len, y) && is_lowercase_segment(s, len, y + 1, z));
              loop assigns j;
              loop variant len - j;
            */
            for (int j = i + 1; j < len; j++) {
                // j will be the end of the first lowercase segment and the position of the underscore

                if (is_char_lowercase_letter(s, len, j) == 1) {
                    // Continue the first lowercase segment
                    continue;
                } else if (is_char_underscore(s, len, j) == 1) {
                    // Found an underscore, now look for the second lowercase segment
                    // The first segment is s[i...j-1]
                    // The underscore is s[j]

                    /*@
                      loop invariant j + 1 <= k && k <= len;
                      loop invariant \forall integer x, y;
                        j + 1 <= x && x < y && y <= k &&
                        !(is_lowercase_segment(s, len, j + 1, x) && is_char_underscore(s, len, x) && is_lowercase_segment(s, len, x + 1, y));
                      loop assigns k;
                      loop variant len - k;
                    */
                    for (int k = j + 1; k <= len; k++) {
                        // k will be the end of the second lowercase segment

                        if (k == len || is_char_lowercase_letter(s, len, k) == 0) {
                            // The second segment ends at k-1.
                            // Check if s[j+1...k-1] is a valid lowercase segment
                            // and s[i...j-1] is a valid lowercase segment
                            if (is_lowercase_segment(s, len, i, j) &&
                                is_lowercase_segment(s, len, j + 1, k)) {
                                return 1;
                            }
                            // If s[k] is not a lowercase letter, then the segment s[j+1...k-1]
                            // is the longest possible lowercase segment starting after the underscore.
                            // We need to break out of this inner loop to find new segments.
                            break;
                        }
                    }
                } else {
                    // Neither a lowercase letter nor an underscore, break the first segment search
                    break;
                }
            }
        }
    }
    return 0; // No sequence found
}
