// Task ID: 15
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Define a logic function to check if a character is a lowercase letter.
  axiomatic IsLower {
    logic int is_lower_char(char c);

    axiom is_lower_char_def:
      \forall char c; is_lower_char(c) == (c >= 'a' && c <= 'z');
  }

  // Define a logic function to check if a character is an uppercase letter.
  axiomatic IsUpper {
    logic int is_upper_char(char c);

    axiom is_upper_char_def:
      \forall char c; is_upper_char(c) == (c >= 'A' && c <= 'Z');
  }

  // Define a logic function to check if a character is a digit.
  axiomatic IsDigit {
    logic int is_digit_char(char c);

    axiom is_digit_char_def:
      \forall char c; is_digit_char(c) == (c >= '0' && c <= '9');
  }

  // Define a logic function to check if a character is a whitespace.
  // For simplicity, we only consider space ' ' as whitespace.
  axiomatic IsSpace {
    logic int is_space_char(char c);

    axiom is_space_char_def:
      \forall char c; is_space_char(c) == (c == ' ');
  }

  // Define a logic function to check if a character is a separator.
  // A separator is defined as a lowercase letter for this problem.
  axiomatic IsSeparator {
    logic int is_separator_char(char c);

    axiom is_separator_char_def:
      \forall char c; is_separator_char(c) == is_lower_char(c);
  }

  // Logic function to count the number of separators in a string up to a given length.
  axiomatic SeparatorCount {
    logic integer count_separators(char *s, integer len);

    axiom count_separators_base:
      \forall char *s; count_separators(s, 0) == 0;

    axiom count_separators_rec:
      \forall char *s, integer len;
        len > 0 ==> count_separators(s, len) == count_separators(s, len - 1) + (is_separator_char(s[len - 1]) ? 1 : 0);

    // Rule II.2: Helper axiom to show that count_separators is non-negative.
    axiom count_separators_non_negative:
      \forall char *s, integer len;
        len >= 0 ==> count_separators(s, len) >= 0;

    // Helper axiom to show that count_separators is non-decreasing.
    axiom count_separators_non_decreasing:
      \forall char *s, integer len1, integer len2;
        0 <= len1 <= len2 ==> count_separators(s, len1) <= count_separators(s, len2);
  }

  // Logic function to determine the length of a string (null-terminated).
  axiomatic StringLength {
    logic integer string_length(char *s);

    axiom string_length_def:
      \forall char *s; string_length(s) == (\exists integer i; s[i] == '\0' && (\forall integer j; 0 <= j < i ==> s[j] != '\0') ? i : -1); // -1 if not null-terminated

    // Helper axiom: string_length is non-negative if null-terminated.
    axiom string_length_non_negative:
      \forall char *s; s[string_length(s)] == '\0' ==> string_length(s) >= 0;
  }

  // Logic function to check if a character is within a valid ASCII range for this problem.
  axiomatic IsValidChar {
    logic int is_valid_char(char c);

    axiom is_valid_char_def:
      \forall char c; is_valid_char(c) == (is_lower_char(c) || is_upper_char(c) || is_digit_char(c) || is_space_char(c) || c == '\0');
  }

  // Logic function to check if a string contains only valid characters.
  axiomatic IsValidString {
    logic int is_valid_string(char *s);

    axiom is_valid_string_def:
      \forall char *s; is_valid_string(s) == (\forall integer i; 0 <= i <= string_length(s) ==> is_valid_char(s[i]));
  }
*/

/*@
  requires s != \null;
  requires is_valid_string(s);
  requires string_length(s) >= 0; // Ensure s is null-terminated.
  requires result != \null; // output array must be allocated
  requires max_rows >= 1; // At least one row for the first word
  // The number of words can be at most string_length(s) + 1 (empty string or all separators).
  // The number of words is at most count_separators(s, string_length(s)) + 1
  // If the string is "abc", 1 word. "a" "bc" -> 2 words.
  // The maximum number of words is string_length(s) + 1 (e.g., "a", "b", "c").
  // So, max_rows must be large enough to hold all potential words.
  requires max_rows >= count_separators(s, string_length(s)) + 1;
  requires max_cols >= string_length(s) + 1; // Each row must be able to hold the longest possible word + null terminator.

  // Rule II.5: Prevent runtime errors.
  // Ensure that indices are always within bounds.
  // This helps WP prove array accesses are safe.
  // For `result[i][j] = ...`, we need `i < max_rows` and `j < max_cols`.

  assigns result[0..max_rows-1][0..max_cols-1];

  // Rule II.3: Ensures clause for boolean-like functions. Not applicable here as it returns void.
  // Instead, describe the post-state of the result array.

  ensures \forall integer i; 0 <= i < \result_num_words ==> result[i][max_cols-1] == '\0'; // All rows are null-terminated.
  ensures \forall integer i; 0 <= i < \result_num_words ==> string_length(result[i]) < max_cols; // Word length within bounds.
  ensures \forall integer i; 0 <= i < \result_num_words ==> \forall integer k; 0 <= k < string_length(result[i]) ==> !is_separator_char(result[i][k]); // No separators within words.
  ensures \forall integer i; 0 <= i < \result_num_words - 1 ==> is_separator_char(s[s_index_mapping(i) + string_length(result[i])]); // Separator after each word (except last)

  // This is a complex post-condition. We need to relate the original string `s`
  // with the `result` array. This might require additional logic functions
  // to define the "split" property precisely.
  // For simplicity, let's aim for a high-level guarantee.

  // The total number of words written to `result`.
  // This implicitly defines how many rows of `result` are used.
  // The return value indicates the number of words found and stored.
  behavior valid:
    assumes \true;
    ensures \result >= 0;
    ensures \result <= max_rows;
    // The total length of all words + separators must be less than or equal to string_length(s).
    // This is hard to express precisely without more logic functions that map original
    // string indices to new word indices.

    // A simpler guarantee: The function correctly identifies and copies
    // non-separator sequences into `result`.
    // The number of words returned should be consistent with the number of separators.
    ensures \result == count_separators(s, string_length(s)) + 1; // This is true if every separator causes a split.
*/
int split_string_at_lowercase(char *s, char **result, int max_rows, int max_cols) {
    int s_len = 0;
    /*@
      loop invariant 0 <= s_len <= string_length(s);
      loop invariant \forall integer k; 0 <= k < s_len ==> s[k] != '\0';
      loop assigns s_len;
      loop variant string_length(s) - s_len;
    */
    while (s[s_len] != '\0') {
        s_len++;
    }

    int current_word_idx = 0; // Current word index in result
    int current_char_idx = 0; // Current character index within the current word
    int i = 0;                // Iterator for the input string s

    /*@
      loop invariant 0 <= i <= s_len;
      loop invariant 0 <= current_word_idx <= max_rows;
      loop invariant 0 <= current_char_idx < max_cols;
      loop invariant (i == 0 && current_word_idx == 0 && current_char_idx == 0) || // Initial state
                     (current_word_idx < max_rows && current_char_idx < max_cols); // Maintain bounds

      // All words processed so far do not contain separators internally.
      loop invariant \forall integer r; 0 <= r < current_word_idx ==> \forall integer c; 0 <= c < string_length(result[r]) ==> !is_separator_char(result[r][c]);

      // All words processed so far are null-terminated and within max_cols.
      loop invariant \forall integer r; 0 <= r < current_word_idx ==> result[r][string_length(result[r])] == '\0';
      loop invariant \forall integer r; 0 <= r < current_word_idx ==> string_length(result[r]) < max_cols;

      // If we are currently building a word, ensure characters copied so far are not separators.
      loop invariant \forall integer c; 0 <= c < current_char_idx ==> !is_separator_char(result[current_word_idx][c]);

      loop assigns i, current_word_idx, current_char_idx, result[0..max_rows-1][0..max_cols-1];
      loop variant s_len - i;
    */
    while (i <= s_len) { // Loop until the null terminator is processed
        /*@
          // Rule III.1: No C-style ternary in ACSL.
          // Rule III.2: No parentheses around if-then-else.
          // Rule III.3: Correct range syntax.
          // Rule III.4: No stray semicolons.
        */
        if (i == s_len || is_separator_char(s[i])) {
            // End of string or a separator encountered, terminate current word.
            if (current_char_idx > 0 || (i == s_len && current_char_idx == 0 && current_word_idx == 0)) {
                // Only terminate if a word was being built, or if it's an empty string case.
                // Or if it's the very first word and it's an empty string.
                // Ensure we don't write beyond allocated row/col.
                /*@ assert current_word_idx < max_rows; */
                /*@ assert current_char_idx < max_cols; */
                result[current_word_idx][current_char_idx] = '\0'; // Null-terminate the current word
                current_word_idx++; // Move to the next word slot
            }
            current_char_idx = 0; // Reset character index for the next word
        } else {
            // Not a separator, copy character to current word.
            /*@ assert current_word_idx < max_rows; */
            /*@ assert current_char_idx < max_cols; */
            result[current_word_idx][current_char_idx] = s[i];
            current_char_idx++;
        }
        i++;
    }

    // Handle the case where the string is empty or ends with a separator,
    // and no words were created, but current_word_idx was incremented.
    // The last increment of current_word_idx might be for an empty word after a trailing separator.
    // We should only count non-empty words.
    // The loop logic above is designed to always increment current_word_idx when a word is completed.
    // If the string starts with a separator, or has consecutive separators, empty words might be
    // created and then immediately terminated.

    // A more robust way to count:
    int actual_words_count = 0;
    /*@
      loop invariant 0 <= actual_words_count <= current_word_idx;
      loop invariant \forall integer k; 0 <= k < actual_words_count ==> string_length(result[k]) > 0 || (current_word_idx == 1 && string_length(result[0]) == 0); // Allow empty string case
      loop assigns actual_words_count;
      loop variant current_word_idx - actual_words_count;
    */
    for (int k = 0; k < current_word_idx; k++) {
        if (result[k][0] != '\0') { // Check if the word is not empty
            actual_words_count++;
        } else if (k == 0 && s_len == 0) { // Special case: empty input string produces one empty word
            actual_words_count++;
        }
    }

    return actual_words_count;
}
