// Task ID: 39
// Generation: 6

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This logic function checks if a string 's' of length 'len' has adjacent identical characters.
  axiomatic HasAdjacentIdentical {
    logic boolean has_adjacent_identical_char(char *s, int len);

    // Rule II.1: Base case for the recursive logic function.
    axiom has_adjacent_identical_char_base:
      \forall char *s, integer len; len <= 1 ==> !has_adjacent_identical_char(s, len);

    // Rule II.1: Recursive case for the logic function.
    axiom has_adjacent_identical_char_rec:
      \forall char *s, integer len; len >= 2 ==>
        (has_adjacent_identical_char(s, len) <==> (s[len-1] == s[len-2] || has_adjacent_identical_char(s, len-1)));
  }
*/

/*@
  // Rule II.1: Define recursive logic for counting character frequencies.
  // This logic function counts the occurrences of a character 'c' in a string 's' up to index 'idx'.
  axiomatic CharCount {
    logic integer count_char_in_prefix(char *s, int idx, char c);

    // Rule II.1: Base case for the recursive logic function.
    axiom count_char_in_prefix_base:
      \forall char *s, char c; count_char_in_prefix(s, -1, c) == 0;

    // Rule II.1: Recursive case for the logic function.
    axiom count_char_in_prefix_rec:
      \forall char *s, integer idx, char c; idx >= 0 ==>
        (count_char_in_prefix(s, idx, c) ==
         (if s[idx] == c then count_char_in_prefix(s, idx-1, c) + 1
          else count_char_in_prefix(s, idx-1, c)));
  }
*/

/*@
  // Rule II.1: Define logic for the maximum frequency of any character in a string.
  axiomatic MaxFrequency {
    logic integer max_freq(char *s, int len);

    // Rule II.1: Base case for max_freq.
    axiom max_freq_base:
      \forall char *s, integer len; len <= 0 ==> max_freq(s, len) == 0;

    // Rule II.1: Recursive case for max_freq.
    // Iterates through all possible characters ('a' to 'z' for simplicity, assuming lowercase alphabet)
    // and finds the maximum count.
    axiom max_freq_rec:
      \forall char *s, integer len; len > 0 ==>
        (max_freq(s, len) ==
         \max(count_char_in_prefix(s, len-1, 'a'),
              count_char_in_prefix(s, len-1, 'b'),
              count_char_in_prefix(s, len-1, 'c'),
              count_char_in_prefix(s, len-1, 'd'),
              count_char_in_prefix(s, len-1, 'e'),
              count_char_in_prefix(s, len-1, 'f'),
              count_char_in_prefix(s, len-1, 'g'),
              count_char_in_prefix(s, len-1, 'h'),
              count_char_in_prefix(s, len-1, 'i'),
              count_char_in_prefix(s, len-1, 'j'),
              count_char_in_prefix(s, len-1, 'k'),
              count_char_in_prefix(s, len-1, 'l'),
              count_char_in_prefix(s, len-1, 'm'),
              count_char_in_prefix(s, len-1, 'n'),
              count_char_in_prefix(s, len-1, 'o'),
              count_char_in_prefix(s, len-1, 'p'),
              count_char_in_prefix(s, len-1, 'q'),
              count_char_in_prefix(s, len-1, 'r'),
              count_char_in_prefix(s, len-1, 's'),
              count_char_in_prefix(s, len-1, 't'),
              count_char_in_prefix(s, len-1, 'u'),
              count_char_in_prefix(s, len-1, 'v'),
              count_char_in_prefix(s, len-1, 'w'),
              count_char_in_prefix(s, len-1, 'x'),
              count_char_in_prefix(s, len-1, 'y'),
              count_char_in_prefix(s, len-1, 'z')));
  }
*/

/*@
  requires \valid_read_range(s, 0, len - 1);
  requires len >= 0;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // A string can be rearranged such that no two adjacent characters are the same
  // if and only if the maximum frequency of any character is not greater than
  // (len + 1) / 2. This is the condition for a valid rearrangement.
  ensures (\result == 1) <==> (max_freq(s, len) <= (len + 1) / 2);
*/
int can_rearrange_no_adjacent_identical(char *s, int len) {
    // Assuming ASCII characters and potentially only lowercase English letters 'a'-'z'
    // for frequency counting. Adapt `ALPHABET_SIZE` and loop bounds if needed.
    // For simplicity, let's assume all possible char values are covered by an array of size 256.
    enum { ALPHABET_SIZE = 256 };
    int freq[ALPHABET_SIZE] = {0}; // Rule I.1: No memset, initialize to 0.

    // Calculate character frequencies
    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < ALPHABET_SIZE ==>
        freq[k] == count_char_in_prefix(s, i-1, (char)k);
      loop assigns i, freq[0..ALPHABET_SIZE-1];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Rule II.5: Prevent out-of-bounds array access.
        // Assumes char values fit within 0..ALPHABET_SIZE-1.
        // This implicitly requires `s[i]` to be a valid index.
        // For general chars, this is true if ALPHABET_SIZE is 256.
        freq[(unsigned char)s[i]]++;
    }

    int max_frequency = 0;
    // Find the maximum frequency
    /*@
      loop invariant 0 <= i <= ALPHABET_SIZE;
      loop invariant max_frequency == \max(
        \for integer k; 0 <= k < i; freq[k]
      );
      loop assigns i, max_frequency;
      loop variant ALPHABET_SIZE - i;
    */
    for (int i = 0; i < ALPHABET_SIZE; i++) {
        if (freq[i] > max_frequency) {
            max_frequency = freq[i];
        }
    }

    // The condition for rearrangement is that the most frequent character
    // does not appear more than (total_length + 1) / 2 times.
    // This is equivalent to max_frequency * 2 <= total_length + 1.
    // Rule II.5: Prevent overflow in max_frequency * 2.
    // Assumes (ALPHABET_SIZE * len) won't cause overflow. max freq can be 'len'.
    // So, len * 2 <= INT_MAX + 1 is the implicit requirement.
    // Given 'len' is likely small for typical string problems, this should hold.
    if (max_frequency * 2 <= len + 1) {
        return 1; // True, can be rearranged
    } else {
        return 0; // False, cannot be rearranged
    }
}
