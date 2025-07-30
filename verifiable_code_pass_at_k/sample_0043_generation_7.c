// Task ID: 43
// Generation: 7

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
  // Axiomatic block to define properties of characters.
  axiomatic CharProperties {
    // Rule II.1: Define recursive logic functions.
    // Checks if a character is a lowercase letter.
    logic boolean is_lower_char(char c) = (c >= 'a' && c <= 'z');

    // Checks if a substring from start to end (exclusive) consists only of lowercase letters.
    // Base case: empty string
    // Recursive case: check first char and rest of string.
    logic boolean is_lower_sequence(char *s, integer start, integer end) reads s[start..end-1];

    axiom is_lower_sequence_base{L}:
      \forall char *s, integer start;
        is_lower_sequence(s, start, start); // An empty sequence is considered a valid "lower sequence".

    axiom is_lower_sequence_rec{L}:
      \forall char *s, integer start, integer end;
        start < end ==>
         (is_lower_sequence(s, start, end) <==>
          (is_lower_char(s[start]) && is_lower_sequence(s, start + 1, end)));

    // Helper axiom (Rule II.2): If a sequence is a lower sequence, all its characters are lower.
    axiom is_lower_sequence_helper{L}:
      \forall char *s, integer start, integer end, integer i;
        is_lower_sequence(s, start, end) && start <= i < end ==> is_lower_char(s[i]);
  }
*/

/*@
  requires \valid_read_string(s);
  requires max_matches >= 0;
  requires \valid(matches + (0..max_matches - 1));

  // Precondition: Ensure the string length won't cause issues with integer arithmetic.
  requires \strlen(s) < INT_MAX;

  assigns matches[0..max_matches-1];

  // Rule II.3: Use logical equivalence for boolean-like return.
  // The function returns the number of matches found.
  // Each match corresponds to a (start, end) pair in the matches array.
  // The postcondition ensures that for each reported match, the pattern holds:
  //   - A lowercase sequence
  //   - Followed by an underscore (if not at the end of the string)
  //   - Followed by another lowercase sequence.
  // It also ensures that no matches are reported beyond the actual number found.
  ensures \result >= 0 && \result <= max_matches;
  ensures \forall integer k; 0 <= k < \result ==>
    (matches[k].start >= 0 && matches[k].end >= matches[k].start &&
     matches[k].end <= \strlen(s) &&
     // First lowercase sequence
     is_lower_sequence(s, matches[k].start, matches[k].start + matches[k].len1) &&
     // Underscore
     s[matches[k].start + matches[k].len1] == '_' &&
     // Second lowercase sequence
     is_lower_sequence(s, matches[k].start + matches[k].len1 + 1, matches[k].end));
  ensures \forall integer k; \result <= k < max_matches ==>
    matches[k].start == 0 && matches[k].len1 == 0 && matches[k].end == 0; // Clear unused entries
*/
int find_regex_matches(char *s, int max_matches, struct Match *matches) {
    int i = 0; // Current index in the string
    int match_count = 0; // Number of matches found
    int s_len = 0;

    /*@
      loop invariant 0 <= i <= \strlen(s);
      loop invariant 0 <= match_count <= max_matches;
      loop invariant \forall integer k; 0 <= k < match_count ==>
        (matches[k].start >= 0 && matches[k].end >= matches[k].start &&
         matches[k].end <= \strlen(s) &&
         is_lower_sequence(s, matches[k].start, matches[k].start + matches[k].len1) &&
         s[matches[k].start + matches[k].len1] == '_' &&
         is_lower_sequence(s, matches[k].start + matches[k].len1 + 1, matches[k].end));
      loop assigns i, match_count, matches[0..max_matches-1];
      loop variant \strlen(s) - i;
    */
    while (s[s_len] != '\0') {
        s_len++;
    }

    /*@
      loop invariant 0 <= i <= s_len;
      loop invariant 0 <= match_count <= max_matches;
      loop invariant \forall integer k; 0 <= k < match_count ==>
        (matches[k].start >= 0 && matches[k].end >= matches[k].start &&
         matches[k].end <= s_len &&
         is_lower_sequence(s, matches[k].start, matches[k].start + matches[k].len1) &&
         s[matches[k].start + matches[k].len1] == '_' &&
         is_lower_sequence(s, matches[k].start + matches[k].len1 + 1, matches[k].end));
      loop assigns i, match_count, matches[0..max_matches-1];
      loop variant s_len - i;
    */
    while (i < s_len && match_count < max_matches) {
        int start_idx = i;
        int len1 = 0;
        int len2 = 0;

        // Find first sequence of lowercase letters
        /*@
          loop invariant start_idx <= i <= s_len;
          loop invariant len1 == i - start_idx;
          loop invariant is_lower_sequence(s, start_idx, i);
          loop assigns i, len1;
          loop variant s_len - i;
        */
        while (i < s_len && is_lower_char(s[i])) {
            len1++;
            i++;
        }

        // Check for underscore
        if (len1 > 0 && i < s_len && s[i] == '_') {
            i++; // Move past '_'
            int underscore_pos = i - 1; // Position of the underscore
            int seq2_start_idx = i;

            // Find second sequence of lowercase letters
            /*@
              loop invariant seq2_start_idx <= i <= s_len;
              loop invariant len2 == i - seq2_start_idx;
              loop invariant is_lower_sequence(s, seq2_start_idx, i);
              loop assigns i, len2;
              loop variant s_len - i;
            */
            while (i < s_len && is_lower_char(s[i])) {
                len2++;
                i++;
            }

            if (len2 > 0) {
                // Found a match
                matches[match_count].start = start_idx;
                matches[match_count].len1 = len1;
                matches[match_count].end = i;
                match_count++;
            } else {
                // If no second sequence, backtrack i to after the first sequence
                // and underscore, so the outer loop doesn't re-evaluate
                // the underscore at the same position.
                // Rule II.5: Prevent RTE by ensuring i doesn't go below 0.
                if (underscore_pos > start_idx) {
                    i = underscore_pos;
                } else {
                    // This case implies len1 was 0, but we checked len1 > 0.
                    // So this else branch should not be reachable if len1 > 0.
                    // For safety, just advance i by one if len1 was 0 (which it wasn't).
                    // Or, simply advance i to the next character after the underscore,
                    // as the underscore itself cannot be the start of a new match.
                    i = underscore_pos + 1;
                }
            }
        } else {
            // No match found starting at start_idx, advance i by one if no characters were consumed
            // or if a partial match failed.
            if (i == start_idx) { // No lowercase sequence found
                i++;
            }
            // If i > start_idx, it means we consumed some lowercase chars but no underscore or second sequence.
            // i is already at the correct position for the next iteration.
        }
    }

    /*@
      loop invariant match_count <= k <= max_matches;
      loop assigns matches[k];
      loop variant max_matches - k;
    */
    for (int k = match_count; k < max_matches; k++) {
        matches[k].start = 0;
        matches[k].len1 = 0;
        matches[k].end = 0;
    }

    return match_count;
}


// Define the struct for Match
struct Match {
    int start; // Start index of the entire match (first char of first sequence)
    int len1;  // Length of the first lowercase sequence
    int end;   // End index (exclusive) of the entire match (one past last char of second sequence)
};
