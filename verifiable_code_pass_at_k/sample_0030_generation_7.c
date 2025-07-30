// Task ID: 30
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Axiomatic definition for counting substrings starting and ending with the same character.
  // This is a recursive logic function as per Rule II.1.
  axiomatic SubstringCount {
    logic integer count_same_char_substrings(char *s, int len);

    // Base case: An empty string has 0 such substrings.
    axiom count_same_char_substrings_empty:
      \forall char *s; count_same_char_substrings(s, 0) == 0;

    // Recursive case:
    // For a string s of length len:
    // It's the count for s[1..len-1] (tail of the string)
    // plus 1 (for the single-character substring s[0])
    // plus the count of substrings starting with s[0] and ending with s[0] within s[1..len-1].
    // This is `sum_matches(s[0], s+1, len-1)`.
    axiom count_same_char_substrings_recursive:
      \forall char *s, integer len;
        len > 0 ==> count_same_char_substrings(s, len) ==
                      count_same_char_substrings(s + 1, len - 1) + 1 + sum_matches(s[0], s + 1, len - 1);

    // Helper logic function to sum matches for a specific character.
    logic integer sum_matches(char c, char *s, int len);

    // Base case for sum_matches: empty string has no matches.
    axiom sum_matches_empty:
      \forall char c, char *s; sum_matches(c, s, 0) == 0;

    // Recursive case for sum_matches:
    // If the first character of s matches c, add 1 plus recursive call for s+1.
    // Else, just recursive call for s+1.
    axiom sum_matches_recursive:
      \forall char c, char *s, integer len;
        len > 0 ==> sum_matches(c, s, len) ==
                      (if s[0] == c then 1 else 0) + sum_matches(c, s + 1, len - 1);
  }
*/

/*@
  requires \valid_read_string(s);
  requires len == \strlen(s);
  requires len >= 0;
  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence.
  ensures \result == count_same_char_substrings(s, len);
*/
int count_substrings(char *s, int len) {
    int count = 0;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant count == count_same_char_substrings(s + i, len - i) + \sum(integer k; 0 <= k < i; 1 + sum_matches(s[k], s + k + 1, len - k - 1));
      // Simplified: count represents the total for s[0..len-1] if we process from right to left.
      // Or, more simply, it accumulates the count of substrings starting at or after index i.
      // Let's refine the invariant to reflect the accumulation from left to right.
      loop invariant count == \sum(integer k; 0 <= k < i; 1 + sum_matches(s[k], s + k + 1, len - k - 1));
      loop assigns count, i, j;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Every single character is a substring starting and ending with itself.
        count++;

        /*@
          loop invariant i + 1 <= j <= len;
          loop invariant count == (\at(count, LoopEntry) + \sum(integer k; i + 1 <= k < j; (s[i] == s[k] ? 1 : 0)));
          loop assigns count, j;
          loop variant len - j;
        */
        for (int j = i + 1; j < len; j++) {
            if (s[i] == s[j]) {
                count++;
            }
        }
    }
    return count;
}
