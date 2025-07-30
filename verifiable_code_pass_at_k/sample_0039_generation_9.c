// Task ID: 39
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  axiomatic CharCount {
    logic integer count_char(char c, char *s, integer len, integer idx);

    axiom count_char_base:
      \forall char c, char *s, integer len;
        count_char(c, s, len, 0) == 0;

    axiom count_char_recursive:
      \forall char c, char *s, integer len, integer idx;
        0 <= idx < len ==>
        count_char(c, s, len, idx + 1) == count_char(c, s, len, idx) + (s[idx] == c ? 1 : 0);

    // Helper axiom: The count of a character is non-negative.
    axiom count_char_ge_zero:
      \forall char c, char *s, integer len, integer idx;
        0 <= idx <= len ==> count_char(c, s, len, idx) >= 0;

    // Helper axiom: The total count of a character up to len is simply count_char(c, s, len, len).
    axiom count_char_total:
      \forall char c, char *s, integer len;
        \sum(0, len - 1, \lambda integer k; (s[k] == c ? 1 : 0)) == count_char(c, s, len, len);
  }
*/

/*@
  requires len >= 0;
  requires \valid_read_range(s, 0, len - 1);
  // Rule II.5: Prevent runtime errors. Max frequency cannot exceed (len + 1) / 2.
  // If len is even, max_freq <= len / 2.
  // If len is odd, max_freq <= (len / 2) + 1.
  // This can be combined to (len + 1) / 2 using integer division.
  // The function returns 1 (true) if a rearrangement is possible.
  // A rearrangement is possible if and only if the frequency of any character
  // is not greater than (len + 1) / 2.

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence.
  ensures (\forall char c; ('a' <= c && c <= 'z') ==> (count_char(c, s, len, len) <= (len + 1) / 2)) <==> (result == 1);
*/
int can_rearrange_adjacent_different(char *s, int len) {
    if (len <= 1) {
        return 1; // Single character or empty string can always be rearranged.
    }

    int freq[26]; // Using an array for frequency counts. 'a' maps to index 0, 'b' to 1, etc.

    /*@
      loop invariant 0 <= i <= 26;
      loop invariant \forall integer k; 0 <= k < i ==> freq[k] == 0;
      loop assigns i, freq[0..25];
      loop variant 26 - i;
    */
    for (int i = 0; i < 26; i++) {
        freq[i] = 0;
    }

    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i ==> 'a' <= s[k] <= 'z'; // Assuming lowercase English letters
      loop invariant \forall integer c_idx; 0 <= c_idx < 26 ==> freq[c_idx] == count_char((char)('a' + c_idx), s, i, i);
      loop assigns i, freq[0..25];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Assuming input string only contains lowercase English letters.
        // Add a requires clause if this assumption is not guaranteed.
        // For this problem, we assume s[i] is always 'a' through 'z'.
        freq[s[i] - 'a']++;
    }

    int max_freq = 0;
    /*@
      loop invariant 0 <= i <= 26;
      loop invariant \forall integer k; 0 <= k < i ==> max_freq >= freq[k];
      loop invariant max_freq >= 0;
      loop assigns i, max_freq;
      loop variant 26 - i;
    */
    for (int i = 0; i < 26; i++) {
        if (freq[i] > max_freq) {
            max_freq = freq[i];
        }
    }

    // A string can be rearranged such that no two adjacent characters are the same
    // if and only if the count of any character is not more than (len + 1) / 2.
    // Rule III.2: No parentheses around if-then-else.
    // Rule III.1: No C-style ternary in ACSL.
    return (max_freq <= (len + 1) / 2);
}
