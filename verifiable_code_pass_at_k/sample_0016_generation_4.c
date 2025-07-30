// Task ID: 16
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  axiomatic LetterSequence {
    logic boolean is_lowercase_letter(char c) = (c >= 'a' && c <= 'z');

    logic integer sequence_length(char *s, integer start_idx, integer max_len)
    reads s[0..max_len-1]; // Rule I.3: Array pointer decay.
    // Rule II.1: Base case for recursion.
    axiom sequence_length_base:
      \forall char *s, integer start_idx, integer max_len;
        start_idx >= max_len ==> sequence_length(s, start_idx, max_len) == 0;
    axiom sequence_length_base_char:
      \forall char *s, integer start_idx, integer max_len;
        start_idx < max_len && !is_lowercase_letter(s[start_idx]) ==> sequence_length(s, start_idx, max_len) == 0;
    // Rule II.1: Recursive case.
    axiom sequence_length_recursive:
      \forall char *s, integer start_idx, integer max_len;
        start_idx < max_len && is_lowercase_letter(s[start_idx]) ==>
          sequence_length(s, start_idx, max_len) == 1 + sequence_length(s, start_idx + 1, max_len);

    // Helper axiom: if a sequence starts with a letter, its length is at least 1.
    // Rule II.2: Helper axioms are critical.
    axiom sequence_length_positive:
      \forall char *s, integer start_idx, integer max_len;
        start_idx < max_len && is_lowercase_letter(s[start_idx]) ==> sequence_length(s, start_idx, max_len) >= 1;

    // Helper axiom: sequence length is never negative.
    axiom sequence_length_non_negative:
      \forall char *s, integer start_idx, integer max_len;
        sequence_length(s, start_idx, max_len) >= 0;

    // Helper axiom: sequence length is bounded by remaining length.
    axiom sequence_length_bounded:
      \forall char *s, integer start_idx, integer max_len;
        sequence_length(s, start_idx, max_len) <= max_len - start_idx;
  }
*/

/*@
  requires \valid_read_range(s, 0, len - 1);
  requires len >= 0;
  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.5: Prevent runtime errors. String s must be valid.
  ensures (\exists integer i;
             0 <= i < len &&
             // Check for a letter sequence
             is_lowercase_letter(s[i]) && sequence_length(s, i, len) >= 1 &&
             // Check for underscore if not at the end of the string
             (i + sequence_length(s, i, len) < len ==> s[i + sequence_length(s, i, len)] == '_') &&
             // Check that the character after the underscore is a letter if underscore exists
             (i + sequence_length(s, i, len) < len && s[i + sequence_length(s, i, len)] == '_' ==>
                i + sequence_length(s, i, len) + 1 < len && is_lowercase_letter(s[i + sequence_length(s, i, len) + 1])
             )
          ) <==> (\result == 1);
*/
int has_letter_underscore_sequence(char *s, int len) {
    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i ==>
        !(is_lowercase_letter(s[k]) && sequence_length(s, k, len) >= 1 &&
          (k + sequence_length(s, k, len) < len ==> s[k + sequence_length(s, k, len)] == '_') &&
          (k + sequence_length(s, k, len) < len && s[k + sequence_length(s, k, len)] == '_' ==>
             k + sequence_length(s, k, len) + 1 < len && is_lowercase_letter(s[k + sequence_length(s, k, len) + 1])
          )
        );
      loop assigns i;
      loop variant len - i; // Rule II.4: Mandatory loop variant.
    */
    for (int i = 0; i < len; ++i) {
        // Find the start of a letter sequence
        if (s[i] >= 'a' && s[i] <= 'z') {
            int seq_start = i;
            /*@
              loop invariant seq_start <= i <= len;
              loop invariant \forall integer k; seq_start <= k < i ==> is_lowercase_letter(s[k]);
              loop assigns i;
              loop variant len - i;
            */
            while (i < len && (s[i] >= 'a' && s[i] <= 'z')) {
                i++;
            }
            int seq_len = i - seq_start;

            // Check if the sequence is followed by an underscore
            if (i < len && s[i] == '_') {
                // Check if the underscore is followed by another letter sequence
                if (i + 1 < len && (s[i + 1] >= 'a' && s[i + 1] <= 'z')) {
                    return 1; // Found a sequence
                }
            }
            // Decrement i because the for loop will increment it again, and we want to check the character after the sequence
            // or the character after the invalid underscore pattern.
            // This is a common pattern when an inner loop advances 'i'.
            i--;
        }
    }
    return 0; // No such sequence found
}
