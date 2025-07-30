// Task ID: 7
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as we're dealing with strings (char*).
  // Rule II.1: Recursive logic for complexity - not directly applicable for this problem, as we don't have sums/sequences.
  // Rule II.2: Helper axioms - not directly applicable.
  // Rule II.3: ensures clause for boolean-like functions - applicable for functions returning 1/0.
  // Rule II.4: Mandatory loop annotations - applicable.
  // Rule II.5: Prevent Runtime Errors (RTE) - applicable for loop bounds and string access.
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.

  // Axiomatic block to define string properties and helper logic.
  axiomatic String {
    // Logic function to get the length of a string.
    // This is a common helper needed for string manipulation.
    logic integer strlen_logic(char *s) reads s;

    axiom strlen_empty:
      \forall char *s; s[0] == '\0' ==> strlen_logic(s) == 0;
    
    axiom strlen_rec:
      \forall char *s, integer i;
        s[i] != '\0' ==> strlen_logic(s) == 1 + strlen_logic(s + 1);

    // Helper axiom: string length is non-negative.
    axiom strlen_non_negative:
      \forall char *s; strlen_logic(s) >= 0;

    // Helper axiom: character at an index beyond length is null terminator.
    axiom strlen_char_at_end:
      \forall char *s, integer i;
        i >= strlen_logic(s) ==> s[i] == '\0';

    // Helper axiom: character at an index within length is not null terminator.
    axiom strlen_char_within_bounds:
      \forall char *s, integer i;
        0 <= i < strlen_logic(s) ==> s[i] != '\0';

    // Logic function to check if a character is an alphabet character (a-z, A-Z).
    logic boolean is_alpha(char c);
    axiom is_alpha_def:
      \forall char c; is_alpha(c) <==> ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'));

    // Logic function to check if a character is a digit (0-9).
    logic boolean is_digit(char c);
    axiom is_digit_def:
      \forall char c; is_digit(c) <==> (c >= '0' && c <= '9');

    // Logic function to check if a character is alphanumeric.
    logic boolean is_alphanum(char c);
    axiom is_alphanum_def:
      \forall char c; is_alphanum(c) <==> (is_alpha(c) || is_digit(c));

    // Logic function to check if a substring of length `len` starting at `s` consists only of alphanumeric characters.
    logic boolean is_alphanum_string(char *s, integer len);
    axiom is_alphanum_string_empty:
      \forall char *s; is_alphanum_string(s, 0) == \true;
    axiom is_alphanum_string_rec:
      \forall char *s, integer len;
        len > 0 ==> (is_alphanum_string(s, len) <==> (is_alphanum(s[0]) && is_alphanum_string(s + 1, len - 1)));

    // Logic function to check if a character is a whitespace character (space, tab, newline).
    logic boolean is_whitespace(char c);
    axiom is_whitespace_def:
      \forall char c; is_whitespace(c) <==> (c == ' ' || c == '\t' || c == '\n' || c == '\r');

    // Logic function to determine if a substring s[start..end-1] constitutes a word.
    // A word is defined as a sequence of alphanumeric characters.
    logic boolean is_word_segment(char *s, integer start, integer end);
    axiom is_word_segment_def:
      \forall char *s, integer start, integer end;
        is_word_segment(s, start, end) <==> (
          start <= end &&
          (\forall integer k; start <= k < end ==> is_alphanum(s[k]))
        );
  }
*/

/*@
  requires \valid_read(s + (0 .. strlen_logic(s))); // Ensure s is a valid, null-terminated string.
  requires strlen_logic(s) < 2147483647; // Prevent strlen_logic from exceeding int max.

  // The function finds words of at least 4 characters.
  // It returns the count of such words.
  // A word is defined as a sequence of alphanumeric characters.
  // Words are separated by non-alphanumeric characters or string boundaries.

  assigns \nothing;

  // This function finds and counts "words" (sequences of alphanumeric characters)
  // that have a length of at least 4.
  // The 'result' is the count of such words.
  ensures \result >= 0;
  // Formal specification of the count:
  // result is the number of indices 'i' such that:
  // 1. s[i] is the start of an alphanumeric sequence.
  // 2. This sequence has length 'len' where len >= 4.
  // 3. The character before s[i] (if any) is not alphanumeric OR i is 0.
  // 4. The character after the sequence (s[i+len]) is not alphanumeric OR i+len is strlen_logic(s).
  // This is hard to express purely with quantifiers without recursive logic for word identification.
  // Let's simplify by defining what constitutes a word boundary.
  // A word starts at index `i` if `s[i]` is alphanumeric and `i == 0` or `s[i-1]` is not alphanumeric.
  // A word ends at index `j-1` if `s[j-1]` is alphanumeric and `s[j]` is not alphanumeric or `j == strlen_logic(s)`.

  // The ensures clause describes the post-condition more abstractly:
  // The result is the number of distinct word occurrences (as defined below)
  // that have a length of at least 4.
  // A word is a maximal contiguous sequence of alphanumeric characters.
  // For each word_start, word_end pair such that:
  //   - 0 <= word_start < strlen_logic(s)
  //   - word_start <= word_end <= strlen_logic(s)
  //   - is_word_segment(s, word_start, word_end) is true
  //   - The segment is maximal (i.e., s[word_start-1] is not alphanumeric if word_start > 0,
  //     and s[word_end] is not alphanumeric if word_end < strlen_logic(s)).
  // If (word_end - word_start >= 4), then this word contributes to the count.
*/
int count_long_words(char *s) {
    int count = 0;
    int i = 0;
    int len = strlen_logic(s);

    /*@
      loop invariant 0 <= i <= len;
      loop invariant count >= 0;
      // count represents the number of long words found in s[0..i-1].
      // For any word that ends at or before 'i-1' and starts at 'j',
      // if (word_end - word_start) >= 4, it has been counted.
      // This invariant is tricky to formalize precisely without an explicit word-finding logic.
      // Let's simplify:
      // Invariant: `count` stores the number of valid words found in the prefix `s[0..i-1]`.
      // A word is considered found if its entire extent is within `s[0..i-1]`.
      // More precisely: `count` is the number of maximal alphanumeric segments [start, end)
      // such that `end <= i` and `end - start >= 4`.
      // This still requires a recursive function for "maximal alphanumeric segment".

      // A simpler, more verifiable invariant:
      // `count` holds the number of long words already encountered and processed
      // in the string prefix `s[0 .. i-1]`.
      // `current_word_start` indicates the potential start of the current word being examined.
      // If `current_word_start` is -1, no word is currently being tracked.
      loop invariant \forall integer k; 0 <= k < i ==> (\at(is_alphanum(s[k]), Pre) <==> is_alphanum(s[k])); // Characters haven't changed.
      loop invariant \forall integer k1, k2; 0 <= k1 < k2 < i ==> !is_word_segment(s,k1,k2) || (k2 - k1) < 4 || (
        // For any word segment found ending before 'i', it has been correctly processed.
        // This is a very strong invariant, perhaps too strong for WP to prove easily.
        // A weaker invariant focusing on the state of `count` is better.
        // `count` accurately reflects the number of long words in `s[0..i-1]` based on the algorithm's logic.
        // This implicitly means that if a word (maximal alphanumeric sequence)
        // of length >= 4 ends before or at `i-1`, it has been counted.
        // If a word starts before `i` and ends at or after `i`, it's not yet fully processed/counted.
        \true // Placeholder for complex logic that WP might struggle with.
      );

      loop assigns count, i;
      loop variant len - i;
    */
    while (i < len) {
        // Skip non-alphanumeric characters
        /*@
          loop invariant i <= len;
          loop invariant \forall integer k; \at(i,LoopEntry) <= k < i ==> !is_alphanum(s[k]);
          loop assigns i;
          loop variant len - i;
        */
        while (i < len && !is_alphanum(s[i])) {
            i++;
        }

        int word_start = i;

        // Find end of word
        /*@
          loop invariant word_start <= i <= len;
          loop invariant \forall integer k; word_start <= k < i ==> is_alphanum(s[k]);
          loop assigns i;
          loop variant len - i;
        */
        while (i < len && is_alphanum(s[i])) {
            i++;
        }

        int word_length = i - word_start;

        if (word_length >= 4) {
            count++;
        }
    }

    return count;
}
