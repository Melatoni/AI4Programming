// Task ID: 39
// Generation: 7

/*@
  axiomatic CharCounts {
    logic integer count_char(char c, char *s, integer len);

    axiom count_char_empty{L}:
      \forall char c, char *s, integer len;
        len <= 0 ==> count_char(c, s, len) == 0;

    axiom count_char_recursive{L}:
      \forall char c, char *s, integer len;
        len > 0 ==> count_char(c, s, len) == (if s[len-1] == c then 1 else 0) + count_char(c, s, len - 1);

    // Helper axiom for sum of counts
    axiom count_char_sum{L}:
      \forall char *s, integer len;
        len > 0 ==> \sum_{i=0}^{len-1} 1 == len; // This is a tautology, but useful for reasoning about counts
        // A more direct helper for character counts:
        // \forall char *s, integer len;
        //   \sum_{c='a'}^{'z'} count_char(c, s, len) == len; // Sum of all char counts equals total length
  }
*/

/*@
  requires \valid_read_range(s, 0, len - 1);
  requires len >= 0;
  // Rule II.5: Prevent potential overflow if len is very large, though not directly an arithmetic op.
  // This helps ensure logic reasoning about len is sound.
  requires len <= 2000000000; // A reasonable upper bound for string length

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return.
  // The string can be rearranged if and only if the count of any character
  // is not more than (len + 1) / 2.
  // (len + 1) / 2 is ceiling(len / 2)
  ensures (\forall char c; count_char(c, s, len) <= (len + 1) / 2) <==> (result == 1);
*/
int can_rearrange_adjacent_different(char *s, int len) {
    if (len <= 1) {
        return 1; // A string of length 0 or 1 always satisfies the condition
    }

    /*@
      loop invariant 0 <= i <= 26;
      loop invariant \forall integer k; 0 <= k < i ==> count_char('a' + k, s, len) <= (len + 1) / 2;
      loop assigns i;
      loop variant 26 - i;
    */
    for (int i = 0; i < 26; i++) { // Iterate through 'a' to 'z'
        char current_char = 'a' + i;
        /*@
          // Local variable for character count
          // This is a common pattern in Frama-C for proving properties over computed values.
          // The prover can then reason about `char_count` using the `count_char` axiomatic.
          // Note: Frama-C does not directly track local variable values in `loop invariant`
          // unless they are part of the loop state. It's better to use the logic function directly
          // in the invariant for the `\forall` part.
        */
        int char_count = 0;
        /*@
          loop invariant 0 <= j <= len;
          loop invariant char_count == count_char(current_char, s, j);
          loop assigns j, char_count;
          loop variant len - j;
        */
        for (int j = 0; j < len; j++) {
            if (s[j] == current_char) {
                char_count++;
            }
        }

        if (char_count > (len + 1) / 2) {
            return 0; // Found a character that appears too many times
        }
    }

    return 1; // No character count exceeded the limit
}
