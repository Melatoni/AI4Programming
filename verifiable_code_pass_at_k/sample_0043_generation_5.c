// Task ID: 43
// Generation: 5

/*@ axiomatic RegexMatcher {
  @   // Rule II.1: Define recursive logic for properties over sequences.
  @   // `is_lowercase_char(c)`: Checks if a character `c` is a lowercase English letter.
  @   logic boolean is_lowercase_char(char c) = (c >= 'a' && c <= 'z');
  @
  @   // `is_lowercase_sequence(s, start, end)`: Checks if the substring s[start..end-1] consists
  @   // only of lowercase English letters.
  @   logic boolean is_lowercase_sequence(char *s, int start, int end) =
  @     (start >= end) ||
  @     (is_lowercase_char(s[start]) && is_lowercase_sequence(s, start + 1, end));
  @
  @   // Rule II.2: Helper axiom for `is_lowercase_sequence`.
  @   // If a sequence is lowercase, then any character within it must be lowercase.
  @   axiom is_lowercase_sequence_char_property:
  @     \forall char *s, integer start, integer end, integer i;
  @       start <= i < end && is_lowercase_sequence(s, start, end) ==> is_lowercase_char(s[i]);
  @
  @   // `is_match_at_pos(s, len, pos)`: Checks if a regex pattern "lowercase_sequence_lowercase_sequence"
  @   // matches starting at index `pos` in string `s` of length `len`.
  @   predicate is_match_at_pos(char *s, int len, int pos) =
  @     pos >= 0 && pos < len &&
  @     \exists integer seq1_start, seq1_end, seq2_start, seq2_end;
  @       seq1_start == pos &&
  @       seq1_end > seq1_start &&
  @       seq1_end < len &&
  @       s[seq1_end] == '_' &&
  @       seq2_start == seq1_end + 1 &&
  @       seq2_end > seq2_start &&
  @       seq2_end <= len &&
  @       is_lowercase_sequence(s, seq1_start, seq1_end) &&
  @       is_lowercase_sequence(s, seq2_start, seq2_end);
  @ }
  @*/

/*@
  @ requires \valid_read(s + (0..len-1));
  @ requires len >= 0;
  @
  @ assigns \nothing;
  @
  @ // Rule II.3: Use logical equivalence for boolean-like return values.
  @ ensures (\exists integer i; 0 <= i < len && is_match_at_pos(s, len, i)) <==> (\result == 1);
  @ ensures (\forall integer i; 0 <= i < len ==> !is_match_at_pos(s, len, i)) <==> (\result == 0);
  @*/
int find_regex_sequence(char *s, int len) {
    /*@
      @ loop invariant 0 <= i <= len;
      @ loop invariant \forall integer k; 0 <= k < i ==> !is_match_at_pos(s, len, k);
      @ loop assigns i;
      @ loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Minimum length for a match: at least one char, an underscore, at least one char (1 + 1 + 1 = 3)
        // So, if len - i < 3, no match is possible from this position.
        if (len - i < 3) {
            continue;
        }

        int seq1_start = i;
        int seq1_end = -1;

        // Find end of first lowercase sequence
        /*@
          @ loop invariant seq1_start <= j <= len;
          @ loop invariant \forall integer k; seq1_start <= k < j ==> is_lowercase_char(s[k]);
          @ loop assigns j, seq1_end;
          @ loop variant len - j;
        */
        for (int j = seq1_start; j < len; j++) {
            if (!is_lowercase_char(s[j])) {
                seq1_end = j;
                break;
            }
            if (j == len - 1) { // Reached end of string, no underscore found
                seq1_end = len;
            }
        }

        // Check if a valid first sequence was found and an underscore follows
        if (seq1_end != -1 && seq1_end > seq1_start && seq1_end < len && s[seq1_end] == '_') {
            int seq2_start = seq1_end + 1;
            int seq2_end = -1;

            // Find end of second lowercase sequence
            /*@
              @ loop invariant seq2_start <= k <= len;
              @ loop invariant \forall integer m; seq2_start <= m < k ==> is_lowercase_char(s[m]);
              @ loop assigns k, seq2_end;
              @ loop variant len - k;
            */
            for (int k = seq2_start; k < len; k++) {
                if (!is_lowercase_char(s[k])) {
                    seq2_end = k;
                    break;
                }
                if (k == len - 1) { // Reached end of string
                    seq2_end = len;
                }
            }

            // Check if a valid second sequence was found
            if (seq2_end != -1 && seq2_end > seq2_start) {
                // We found a match
                return 1;
            }
        }
    }

    // No match found after checking all positions
    return 0;
}
