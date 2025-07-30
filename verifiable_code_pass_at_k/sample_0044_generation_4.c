// Task ID: 44
// Generation: 4

/*@
  // Axiomatic definition for checking if a string (s) matches a word (w)
  // starting at a given index (idx) and having a specific length (len).
  // This is used to define the property of a match.
  axiomatic StringMatch {
    logic boolean is_match_at(char* s, int s_len, char* w, int w_len, int idx)
      reads s[0..s_len-1], w[0..w_len-1];

    // Base case: If word length is 0, it's always a match (empty word matches anywhere).
    axiom is_match_at_base:
      \forall char* s, int s_len, char* w, int w_len, int idx;
        w_len == 0 ==> is_match_at(s, s_len, w, w_len, idx);

    // Recursive case: A match exists if the current characters match and the rest of the word matches.
    axiom is_match_at_rec:
      \forall char* s, int s_len, char* w, int w_len, int idx;
        w_len > 0 &&
        idx >= 0 && idx + w_len <= s_len && // Ensure indices are within bounds
        s[idx] == w[0] &&
        is_match_at(s, s_len, w + 1, w_len - 1, idx + 1)
        ==> is_match_at(s, s_len, w, w_len, idx);
  }
*/

/*@
  requires \valid_read(s + (0..s_len-1));
  requires \valid_read(w + (0..w_len-1));
  requires s_len >= 0;
  requires w_len >= 0;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function returns 1 (true) if and only if the word 'w' matches the beginning of 's'.
  ensures (w_len <= s_len && is_match_at(s, s_len, w, w_len, 0)) <==> (\result == 1);
*/
int match_word_at_beginning(char* s, int s_len, char* w, int w_len) {
    // If the word is longer than the string, it cannot be a match.
    if (w_len > s_len) {
        return 0;
    }

    /*@
      loop invariant 0 <= i <= w_len;
      // All characters processed so far match.
      loop invariant \forall integer k; 0 <= k < i ==> s[k] == w[k];
      loop assigns i;
      loop variant w_len - i;
    */
    for (int i = 0; i < w_len; ++i) {
        if (s[i] != w[i]) {
            return 0; // Mismatch found
        }
    }

    // If the loop completes, all characters matched.
    return 1;
}
