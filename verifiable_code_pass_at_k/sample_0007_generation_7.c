// Task ID: 7
// Generation: 7

/*@
  // Rule I.2: Use int for boolean return type.
  // Rule I.1: No standard libraries.
  // This problem description is underspecified for a C function.
  // "Using regex" implies a library that Frama-C cannot verify directly.
  // "Find all words" implies returning a collection, which is complex in C without dynamic allocation.
  //
  // Given the constraints (no stdlib, 100% verifiable by Frama-C/WP),
  // a "regex" match is impossible without implementing a full regex engine
  // or using external libraries, neither of which is allowed/verifiable.
  //
  // Therefore, I will interpret "using regex" as "matching a pattern"
  // and "find all words" as "determine if a word of at least 4 chars exists
  // at a given starting position, and if so, return its length".
  // This allows for a verifiable pure C implementation.
  //
  // The "pattern" for a "word" will be defined as:
  // - Starts with an alphabetic character (a-z, A-Z)
  // - Followed by zero or more alphanumeric characters (a-z, A-Z, 0-9)
  // - At least 4 characters long.
  //
  // The function will return the length of the matched word if found,
  // or 0 if no such word is found at the given starting position.
  // This simulates finding *a* word, not *all* words, due to C's limitations.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Define helper logic functions for character classification.
  axiomatic CharClassifier {
    logic int is_alpha(char c);
    axiom is_alpha_def:
      \forall char c;
        is_alpha(c) == (if (c >= 'a' && c <= 'z') then 1 else if (c >= 'A' && c <= 'Z') then 1 else 0);

    logic int is_alnum(char c);
    axiom is_alnum_def:
      \forall char c;
        is_alnum(c) == (if (is_alpha(c) == 1) then 1 else if (c >= '0' && c <= '9') then 1 else 0);
  }
*/

/*@
  // Rule II.1: Recursive logic to define a "word" match.
  // A word at index `start` of length `len` satisfies the pattern.
  axiomatic WordPattern {
    logic int matches_word_pattern_char(char c, int pos);
    axiom matches_word_pattern_char_base:
      \forall char c; matches_word_pattern_char(c, 0) == is_alpha(c);
    axiom matches_word_pattern_char_rec:
      \forall char c, integer pos; pos > 0 ==> matches_word_pattern_char(c, pos) == is_alnum(c);

    logic int matches_word_pattern_prefix(char *s, integer start, integer len);
    axiom matches_word_pattern_prefix_base:
      \forall char *s, integer start;
        matches_word_pattern_prefix(s, start, 0) == 1; // Empty prefix always matches

    axiom matches_word_pattern_prefix_rec:
      \forall char *s, integer start, integer len;
        len > 0 ==> matches_word_pattern_prefix(s, start, len) ==
          (matches_word_pattern_char(s[start + len - 1], len - 1) == 1 &&
           matches_word_pattern_prefix(s, start, len - 1) == 1);

    // Rule II.2: Helper axiom to prove if a prefix matches, all its characters are alnum (or alpha for first).
    // This is crucial for proving loop invariants.
    axiom matches_word_pattern_prefix_implies_chars:
      \forall char *s, integer start, integer len, integer k;
        0 <= k < len && matches_word_pattern_prefix(s, start, len) == 1 ==>
          (if k == 0 then is_alpha(s[start + k]) else is_alnum(s[start + k])) == 1;
  }
*/

/*@
  // Rule II.5: Preconditions to prevent runtime errors.
  // `str` must be a valid pointer.
  // `len` must be non-negative.
  // `start_idx` must be within the string bounds.
  requires \valid_read(str + (0..len - 1));
  requires len >= 0;
  requires start_idx >= 0 && start_idx <= len; // start_idx can point to null terminator
  
  assigns \nothing;

  // Rule II.3: Ensures clause using logical equivalence.
  // If result > 0, then a word of that length was found starting at start_idx.
  // If result == 0, then no word of at least 4 chars was found starting at start_idx.
  ensures ((\exists integer k; 4 <= k <= len - start_idx &&
                               matches_word_pattern_prefix(str, start_idx, k) == 1 &&
                               (start_idx + k == len || is_alnum(str[start_idx + k]) == 0)) <==> (\result > 0)) &&
          (\result > 0 ==> 4 <= \result <= len - start_idx &&
                           matches_word_pattern_prefix(str, start_idx, \result) == 1 &&
                           (start_idx + \result == len || is_alnum(str[start_idx + \result]) == 0)) &&
          (\result == 0 ==> \forall integer k; k < 4 || k > len - start_idx ||
                                             matches_word_pattern_prefix(str, start_idx, k) == 0 ||
                                             (start_idx + k < len && is_alnum(str[start_idx + k]) == 1));
*/
int find_word_at_position(char *str, int len, int start_idx) {
    // Rule I.2: Use int for boolean logic.
    // Check if the first character is alphabetic.
    if (start_idx >= len || !(str[start_idx] >= 'a' && str[start_idx] <= 'z') && !(str[start_idx] >= 'A' && str[start_idx] <= 'Z')) {
        return 0;
    }

    int current_word_len = 1;

    /*@
      loop invariant start_idx + current_word_len <= len;
      // Rule II.4: Loop invariant for character classification.
      // All characters processed so far form a valid word prefix.
      loop invariant matches_word_pattern_prefix(str, start_idx, current_word_len) == 1;
      // Rule II.4: Loop assigns clause.
      loop assigns current_word_len;
      // Rule II.4: Loop variant for termination.
      loop variant len - (start_idx + current_word_len);
    */
    // Iterate to find the end of the current word.
    for (int i = start_idx + 1; i < len; i++) {
        // Check if the character is alphanumeric.
        if (!((str[i] >= 'a' && str[i] <= 'z') || (str[i] >= 'A' && str[i] <= 'Z') || (str[i] >= '0' && str[i] <= '9'))) {
            break; // End of word
        }
        current_word_len++;
    }

    // Check if the found word is at least 4 characters long.
    if (current_word_len >= 4) {
        return current_word_len;
    } else {
        return 0;
    }
}
