// Task ID: 7
// Generation: 8

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

/*@ axiomatic WordMatcher {
  logic boolean is_word_char(char c);

  axiom is_word_char_def:
    \forall char c; is_word_char(c) <==> ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9'));

  logic integer word_length_at(char *s, integer start_idx, integer len);

  // Base case: If start_idx is out of bounds or not a word char, length is 0.
  axiom word_length_at_base:
    \forall char *s, integer start_idx, integer len;
      (start_idx < 0 || start_idx >= len || !is_word_char(s[start_idx])) ==> word_length_at(s, start_idx, len) == 0;

  // Recursive case: If it's a word char, add 1 and recurse.
  axiom word_length_at_recursive:
    \forall char *s, integer start_idx, integer len;
      (start_idx >= 0 && start_idx < len && is_word_char(s[start_idx])) ==>
        word_length_at(s, start_idx, len) == 1 + word_length_at(s, start_idx + 1, len);

  // Helper axiom: word_length_at is non-negative.
  axiom word_length_at_non_negative:
    \forall char *s, integer start_idx, integer len;
      word_length_at(s, start_idx, len) >= 0;

  // Helper axiom: If a character is not a word character, the word length starting there is 0.
  axiom word_length_at_not_word_char:
    \forall char *s, integer start_idx, integer len;
      (start_idx >= 0 && start_idx < len && !is_word_char(s[start_idx])) ==>
        word_length_at(s, start_idx, len) == 0;

  // Helper axiom: If a word char is followed by a non-word char, the length is 1 + length of subsequent word chars.
  axiom word_length_at_word_char_followed_by_non_word_char:
    \forall char *s, integer start_idx, integer len;
      (start_idx >= 0 && start_idx < len - 1 && is_word_char(s[start_idx]) && !is_word_char(s[start_idx+1])) ==>
        word_length_at(s, start_idx, len) == 1;

  // Helper axiom: If a word char is followed by another word char.
  axiom word_length_at_word_char_followed_by_word_char:
    \forall char *s, integer start_idx, integer len;
      (start_idx >= 0 && start_idx < len - 1 && is_word_char(s[start_idx]) && is_word_char(s[start_idx+1])) ==>
        word_length_at(s, start_idx, len) == 1 + word_length_at(s, start_idx + 1, len);


  logic integer next_word_start(char *s, integer current_idx, integer len);

  // Base case: If current_idx reaches or exceeds len, there's no next word start.
  axiom next_word_start_base:
    \forall char *s, integer current_idx, integer len;
      (current_idx >= len) ==> next_word_start(s, current_idx, len) == len;

  // Recursive case: If current char is a word char, it's the start. Else, skip and find next.
  axiom next_word_start_recursive:
    \forall char *s, integer current_idx, integer len;
      (current_idx < len) ==>
        next_word_start(s, current_idx, len) == (if is_word_char(s[current_idx]) then current_idx else next_word_start(s, current_idx + 1, len));

  // Helper axiom: next_word_start is always >= current_idx.
  axiom next_word_start_ge_current_idx:
    \forall char *s, integer current_idx, integer len;
      next_word_start(s, current_idx, len) >= current_idx;

  // Helper axiom: If next_word_start is less than len, then s[next_word_start] must be a word char.
  axiom next_word_start_is_word_char:
    \forall char *s, integer current_idx, integer len;
      (next_word_start(s, current_idx, len) < len) ==> is_word_char(s[next_word_start(s, current_idx, len)]);

  // Helper axiom: All characters between current_idx and next_word_start (exclusive) are not word characters.
  axiom next_word_start_preceding_chars_not_word_char:
    \forall char *s, integer current_idx, integer len;
      \forall integer k; (current_idx <= k < next_word_start(s, current_idx, len)) ==> !is_word_char(s[k]);

  logic integer count_long_words_in_range(char *s, integer start_idx, integer end_idx, integer min_len);

  // Base case: If start_idx is out of range or no more characters to process.
  axiom count_long_words_in_range_base:
    \forall char *s, integer start_idx, integer end_idx, integer min_len;
      (start_idx >= end_idx) ==> count_long_words_in_range(s, start_idx, end_idx, min_len) == 0;

  // Recursive case: Find the next word, check its length, and recurse.
  axiom count_long_words_in_range_recursive:
    \forall char *s, integer start_idx, integer end_idx, integer min_len;
      (start_idx < end_idx) ==>
        count_long_words_in_range(s, start_idx, end_idx, min_len) ==
          (if next_word_start(s, start_idx, end_idx) < end_idx
           then
             (if word_length_at(s, next_word_start(s, start_idx, end_idx), end_idx) >= min_len
              then 1
              else 0) + count_long_words_in_range(s, next_word_start(s, start_idx, end_idx) + word_length_at(s, next_word_start(s, start_idx, end_idx), end_idx), end_idx, min_len)
           else 0);

  // Helper axiom: If no word is found in the range, count is 0.
  axiom count_long_words_in_range_no_word:
    \forall char *s, integer start_idx, integer end_idx, integer min_len;
      (next_word_start(s, start_idx, end_idx) >= end_idx) ==> count_long_words_in_range(s, start_idx, end_idx, min_len) == 0;

  // Helper axiom: The count is non-negative.
  axiom count_long_words_in_range_non_negative:
    \forall char *s, integer start_idx, integer end_idx, integer min_len;
      count_long_words_in_range(s, start_idx, end_idx, min_len) >= 0;

  // Helper axiom: The count is bounded by the length of the string.
  axiom count_long_words_in_range_upper_bound:
    \forall char *s, integer start_idx, integer end_idx, integer min_len;
      count_long_words_in_range(s, start_idx, end_idx, min_len) <= (end_idx - start_idx);

}
*/

/*@
  requires \valid_read(s + (0..len - 1));
  requires len >= 0;
  requires min_len >= 0;

  assigns \nothing;

  ensures \result >= 0;
  ensures \result == count_long_words_in_range(s, 0, len, min_len);
*/
int find_long_words(char *s, int len, int min_len) {
  int count = 0;
  int i = 0;

  /*@
    loop invariant 0 <= i <= len;
    loop invariant \forall integer k; 0 <= k < i ==> !is_word_char(s[k]) || word_length_at(s, next_word_start(s, 0, len), len) >= min_len; // This is a simplification. The actual invariant is:
    loop invariant count == count_long_words_in_range(s, 0, i, min_len);
    loop assigns i, count;
    loop variant len - i;
  */
  while (i < len) {
    /*@
      loop invariant i <= j <= len;
      loop invariant \forall integer k; i <= k < j ==> !is_word_char(s[k]);
      loop assigns j;
      loop variant len - j;
    */
    while (i < len && !is_word_char(s[i])) {
      i++;
    }

    if (i < len) { // Found a word start
      int word_start = i;
      /*@
        loop invariant word_start <= i <= len;
        loop invariant \forall integer k; word_start <= k < i ==> is_word_char(s[k]);
        loop assigns i;
        loop variant len - i;
      */
      while (i < len && is_word_char(s[i])) {
        i++;
      }
      int word_length = i - word_start;
      if (word_length >= min_len) {
        count++;
      }
    }
  }
  return count;
}
