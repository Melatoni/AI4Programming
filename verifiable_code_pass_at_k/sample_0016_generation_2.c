// Task ID: 16
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled by ACSL logic functions.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic CharProperties {
    logic boolean is_lowercase(char c) = (c >= 'a' && c <= 'z');
  }
*/

/*@
  axiomatic StringMatching {
    // Helper function: Checks if char at index `idx` is lowercase.
    logic boolean is_char_lowercase(char *s, integer idx, integer len) =
      (idx >= 0 && idx < len && is_lowercase(s[idx]));

    // Helper function: Checks if char at index `idx` is an underscore.
    logic boolean is_char_underscore(char *s, integer idx, integer len) =
      (idx >= 0 && idx < len && s[idx] == '_');

    // Recursive logic function to check if a substring from `start` to `end`
    // consists entirely of lowercase letters.
    logic boolean is_sequence_lowercase(char *s, integer len, integer start, integer end) =
      (start > end) ||
      (is_char_lowercase(s, start, len) && is_sequence_lowercase(s, len, start + 1, end));

    // Helper axiom: If a sequence is lowercase, and a char within it is lowercase.
    // This axiom helps the prover deduce properties from the recursive definition.
    axiom is_sequence_lowercase_char_lemma:
      \forall char *s, integer len, integer start, integer end, integer k;
        (0 <= start <= k <= end < len && is_sequence_lowercase(s, len, start, end)) ==> is_char_lowercase(s, k, len);

    // Main logic function: checks if a match exists starting at `idx`.
    // A match is: lowercase sequence, '_', lowercase sequence.
    logic boolean match_at_index(char *s, integer len, integer idx) =
      \exists integer k1, k2;
        0 <= idx && idx + k1 < len && k1 > 0 && // First lowercase sequence (k1 chars)
        is_sequence_lowercase(s, len, idx, idx + k1 - 1) &&
        idx + k1 < len && is_char_underscore(s, idx + k1, len) && // Underscore
        idx + k1 + 1 < len && k2 > 0 && // Second lowercase sequence (k2 chars)
        is_sequence_lowercase(s, len, idx + k1 + 1, idx + k1 + 1 + k2 - 1);

    // Logic function to check if a match exists anywhere in the string.
    logic boolean has_match(char *s, integer len) =
      \exists integer i; 0 <= i < len && match_at_index(s, len, i);
  }
*/

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;
  // Rule II.5: Prevent RTE. Max length for reasonable string processing.
  // Assuming a practical limit for `len` to avoid potential issues with very long strings
  // and to ensure termination proofs are manageable.
  // Given no specific limit, we choose a value that allows for at least a minimal match (a_b).
  requires len <= 10000;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return.
  ensures has_match(s, len) <==> (\result == 1);
*/
int find_sequence(char *s, int len) {
    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i ==> !match_at_index(s, len, k);
      loop assigns i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        /*@
          loop invariant 0 <= k1 <= len - i;
          loop invariant \forall integer k_inner;
            0 <= k_inner < k1 ==> !(\exists integer k2;
              i + k_inner < len && // First part
              is_sequence_lowercase(s, len, i, i + k_inner - 1) &&
              i + k_inner < len && is_char_underscore(s, i + k_inner, len) &&
              i + k_inner + 1 < len && k2 > 0 && // Second part
              is_sequence_lowercase(s, len, i + k_inner + 1, i + k_inner + 1 + k2 - 1)
            );
          loop assigns k1;
          loop variant (len - i) - k1;
        */
        for (int k1 = 1; i + k1 < len; k1++) { // k1 is length of first lowercase sequence
            // Check if s[i]...s[i+k1-1] is lowercase
            int first_seq_is_lowercase = 1;
            /*@
              loop invariant 0 <= j <= k1;
              loop invariant \forall integer m; 0 <= m < j ==> is_char_lowercase(s, i + m, len);
              loop assigns j;
              loop variant k1 - j;
            */
            for (int j = 0; j < k1; j++) {
                if (!is_lowercase(s[i + j])) {
                    first_seq_is_lowercase = 0;
                    break;
                }
            }

            if (first_seq_is_lowercase) {
                // Check for underscore
                if (s[i + k1] == '_') {
                    /*@
                      loop invariant 0 <= k2 <= len - (i + k1 + 1);
                      loop invariant \forall integer k_inner;
                        0 <= k_inner < k2 ==> !(\exists integer k1_dummy; // Dummy k1 to match outer loop structure
                          i + k1_dummy < len &&
                          is_sequence_lowercase(s, len, i, i + k1_dummy - 1) &&
                          i + k1_dummy < len && is_char_underscore(s, i + k1_dummy, len) &&
                          i + k1_dummy + 1 < len && k_inner > 0 &&
                          is_sequence_lowercase(s, len, i + k1_dummy + 1, i + k1_dummy + 1 + k_inner - 1)
                        );
                      loop assigns k2;
                      loop variant (len - (i + k1 + 1)) - k2;
                    */
                    for (int k2 = 1; i + k1 + 1 + k2 <= len; k2++) { // k2 is length of second lowercase sequence
                        // Check if s[i+k1+1]...s[i+k1+1+k2-1] is lowercase
                        int second_seq_is_lowercase = 1;
                        /*@
                          loop invariant 0 <= j <= k2;
                          loop invariant \forall integer m; 0 <= m < j ==> is_char_lowercase(s, i + k1 + 1 + m, len);
                          loop assigns j;
                          loop variant k2 - j;
                        */
                        for (int j = 0; j < k2; j++) {
                            if (!is_lowercase(s[i + k1 + 1 + j])) {
                                second_seq_is_lowercase = 0;
                                break;
                            }
                        }

                        if (second_seq_is_lowercase) {
                            return 1; // Found a match
                        }
                    }
                }
            }
        }
    }
    return 0; // No match found
}
