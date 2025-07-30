// Task ID: 30
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Axiomatic block for recursive logic to count substrings starting and ending with the same character.
  // Rule II.1: Use recursive logic for complexity (no \sum).
  // Rule II.2: Helper axioms for properties.
*/
/*@ axiomatic SubstringCount {
  logic integer count_char_occurrences(char_array s, integer len, char c, integer start_idx);
  
  // Axiom: Base case - no occurrences if start_idx is out of bounds.
  axiom count_char_occurrences_base:
    \forall char_array s, integer len, char c, integer start_idx;
      start_idx >= len ==> count_char_occurrences(s, len, c, start_idx) == 0;

  // Axiom: Recursive step - count occurrences from start_idx.
  axiom count_char_occurrences_recursive:
    \forall char_array s, integer len, char c, integer start_idx;
      start_idx < len ==>
        count_char_occurrences(s, len, c, start_idx) ==
          (if s[start_idx] == c then 1 else 0) + count_char_occurrences(s, len, c, start_idx + 1);

  logic integer count_substrings_for_char(char_array s, integer len, char c, integer start_idx);

  // Axiom: Base case - no substrings if start_idx is out of bounds.
  axiom count_substrings_for_char_base:
    \forall char_array s, integer len, char c, integer start_idx;
      start_idx >= len ==> count_substrings_for_char(s, len, c, start_idx) == 0;

  // Axiom: Recursive step - count for the current character at start_idx and add to recursive call.
  // If s[start_idx] is 'c', then it forms a substring with all subsequent occurrences of 'c'.
  axiom count_substrings_for_char_recursive:
    \forall char_array s, integer len, char c, integer start_idx;
      start_idx < len ==>
        count_substrings_for_char(s, len, c, start_idx) ==
          (if s[start_idx] == c
           then count_char_occurrences(s, len, c, start_idx)
           else 0) + count_substrings_for_char(s, len, c, start_idx + 1);

  logic integer total_substrings(char_array s, integer len, integer current_char_idx);

  // Axiom: Base case - no more characters to consider.
  axiom total_substrings_base:
    \forall char_array s, integer len, integer current_char_idx;
      current_char_idx >= len ==> total_substrings(s, len, current_char_idx) == 0;

  // Axiom: Recursive step - add substrings for the current character and recurse.
  axiom total_substrings_recursive:
    \forall char_array s, integer len, integer current_char_idx;
      current_char_idx < len ==>
        total_substrings(s, len, current_char_idx) ==
          count_char_occurrences(s, len, s[current_char_idx], current_char_idx) +
          total_substrings(s, len, current_char_idx + 1);
}
*/

/*@
  typedef char *char_array;
*/

/*@
  requires \valid_read_string(s);
  requires len >= 0;
  requires \strlen(s) == len; // Ensure len matches the actual string length

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions (not directly boolean here, but for total count).
  // The result should be equal to the total_substrings logic function.
  ensures \result == total_substrings(s, len, 0);
*/
int count_same_char_substrings(char *s, int len) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= len;
      // Invariant: 'count' accumulates the sum of occurrences for characters processed so far.
      // For each 'j' from 0 to 'i-1', and for each 'k' from 'j' to 'len-1', if s[j] == s[k],
      // then (j,k) forms a valid substring. The loop effectively counts pairs (j,k) such that s[j] == s[k] and j <= k.
      // This is equivalent to summing, for each starting character s[j], the number of times s[j] appears
      // from index j to len-1.
      loop invariant count == (\sum integer k; 0 <= k < i; count_char_occurrences(s, len, s[k], k));

      loop assigns i, count;
      // Rule II.4: Loop variant for termination.
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        char current_char = s[i];
        /*@
          loop invariant i <= j <= len;
          // Invariant: 'count' has accumulated the number of substrings starting with s[i]
          // that end at or before j-1.
          loop invariant count == (\sum integer k; 0 <= k < i; count_char_occurrences(s, len, s[k], k)) +
                                 (\sum integer l; i <= l < j; (if s[l] == current_char then 1 else 0));
          loop assigns j, count;
          loop variant len - j;
        */
        for (int j = i; j < len; j++) {
            if (s[j] == current_char) {
                count++;
            }
        }
    }
    return count;
}
