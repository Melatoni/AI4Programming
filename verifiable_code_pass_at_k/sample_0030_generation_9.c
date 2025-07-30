// Task ID: 30
// Generation: 9

/*@
  // Axiomatic block for recursive logic and helper axioms (Rule II.1, II.2)
  axiomatic SubstringCount {
    logic integer count_char_occurrences{L}(char c, char *s, integer start, integer end);

    // Base case: If the range is empty or invalid, count is 0.
    axiom count_char_occurrences_base_empty{L}:
      orall char c, char *s, integer start, integer end;
        start >= end ==> count_char_occurrences(c, s, start, end) == 0;

    // Recursive case: If the character at 'start' matches 'c', increment count and recurse.
    axiom count_char_occurrences_recursive_match{L}:
      orall char c, char *s, integer start, integer end;
        start < end && s[start] == c ==>
          count_char_occurrences(c, s, start, end) == 1 + count_char_occurrences(c, s, start + 1, end);

    // Recursive case: If the character at 'start' does not match 'c', recurse without incrementing.
    axiom count_char_occurrences_recursive_no_match{L}:
      orall char c, char *s, integer start, integer end;
        start < end && s[start] != c ==>
          count_char_occurrences(c, s, start, end) == count_char_occurrences(c, s, start + 1, end);

    // Helper axiom: The count is non-negative.
    axiom count_char_occurrences_helper_non_negative{L}:
      orall char c, char *s, integer start, integer end;
        count_char_occurrences(c, s, start, end) >= 0;

    // Helper axiom: The count is at most the length of the substring.
    axiom count_char_occurrences_helper_upper_bound{L}:
      orall char c, char *s, integer start, integer end;
        count_char_occurrences(c, s, start, end) <= end - start;
  }
*/

/*@
  requires \valid_read_string(s);
  requires len >= 0;
  // Rule II.5: Prevent potential overflow if len is very large, though unlikely for string length.
  // The maximum number of substrings is len * (len + 1) / 2.
  // For len = 65535, this is approx 2 * 10^9, which fits in int.
  // For len = 92681, this is approx 4.2 * 10^9, which overflows signed int.
  // Let's assume len is such that the total count does not overflow int.
  requires len <= 65535; // Max len for count to fit in signed int.

  assigns \nothing;

  ensures \result >= 0;
  // The core logic of the function, expressed as a summation over characters.
  // For each character s[i], count how many times it appears from i to len-1.
  // The total count is the sum of these counts.
  ensures \result == (\sum integer i; 0 <= i < len; count_char_occurrences(s[i], s, i, len));
*/
int count_substrings_same_char(char *s, int len) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant count == (\sum integer k; 0 <= k < i; count_char_occurrences(s[k], s, k, len));
      loop assigns i, count;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        /*@
          loop invariant i <= j <= len;
          loop invariant count == (\sum integer k; 0 <= k < i; count_char_occurrences(s[k], s, k, len)) +
                                 count_char_occurrences(s[i], s, i, j);
          loop assigns j, count; // count is assigned because it increments in this loop
          loop variant len - j;
        */
        for (int j = i; j < len; j++) {
            if (s[i] == s[j]) {
                count++;
            }
        }
    }
    return count;
}
