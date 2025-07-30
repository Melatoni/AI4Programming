// Task ID: 39
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Axiomatic block for recursive logic to count character frequencies.
  // Rule II.1: Use recursive logic for complexity.
  axiomatic CharCount {
    logic integer char_count_rec(char *s, integer start, integer end, char c);

    // Axiom for the base case: empty string or single character not matching.
    axiom char_count_rec_base:
      \forall char *s, integer start, integer end, char c;
        (start >= end) ==> (char_count_rec(s, start, end, c) == 0);

    // Axiom for the recursive step.
    axiom char_count_rec_rec:
      \forall char *s, integer start, integer end, char c;
        (start < end) ==> (char_count_rec(s, start, end, c) ==
                           (if s[start] == c then 1 else 0) + char_count_rec(s, start + 1, end, c));

    // Helper logic function to get the total length of the string.
    logic integer string_length(char *s);

    axiom string_length_base:
      \forall char *s; s[0] == '\0' ==> string_length(s) == 0;

    axiom string_length_rec:
      \forall char *s; s[0] != '\0' ==> string_length(s) == 1 + string_length(s + 1);

    // Main logic function to count character occurrences in a string.
    logic integer char_count(char *s, char c) = char_count_rec(s, 0, string_length(s), c);

    // Helper logic function to find the maximum frequency of any character.
    logic integer max_freq_rec(char *s, integer i, integer len);

    axiom max_freq_rec_base:
      \forall char *s, integer i, integer len;
        (i >= 256) ==> (max_freq_rec(s, i, len) == 0);

    axiom max_freq_rec_rec:
      \forall char *s, integer i, integer len;
        (i < 256) ==> (max_freq_rec(s, i, len) ==
                       \max(char_count(s, (char)i), max_freq_rec(s, i + 1, len)));

    logic integer max_freq(char *s) = max_freq_rec(s, 0, string_length(s));
  }
*/

/*@
  requires \valid_read(s);
  requires \for_all integer k; 0 <= k < string_length(s) ==> \valid_read(s + k);
  requires s[string_length(s)] == '\0'; // Null-terminated string

  // Rule II.5: Prevent runtime errors. String length must not be negative.
  // This is implicitly handled by `string_length >= 0`.
  // No arithmetic operations that could overflow for typical string lengths.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // A string can be rearranged such that adjacent characters are different
  // if and only if the frequency of the most frequent character is not
  // greater than (length + 1) / 2.
  ensures (max_freq(s) <= (string_length(s) + 1) / 2) <==> (result == 1);
*/
int can_rearrange_adjacent_different(char *s) {
    int freq[256] = {0}; // Frequencies for ASCII characters
    int len = 0;

    /*@
      loop invariant 0 <= len;
      loop invariant \for_all integer k; 0 <= k < 256 ==> freq[k] == char_count_rec(s, 0, len, (char)k);
      loop invariant \valid_read(s + len);
      loop assigns len, freq[0..255];
      loop variant string_length(s) - len;
    */
    while (s[len] != '\0') {
        // Rule II.5: Ensure s[len] is a valid index for freq array.
        // Assumes ASCII characters (0-255).
        freq[(unsigned char)s[len]]++;
        len++;
    }

    int max_frequency = 0;
    /*@
      loop invariant 0 <= i && i <= 256;
      loop invariant \for_all integer k; 0 <= k < i ==> max_frequency >= freq[k];
      loop invariant max_frequency == max_freq_rec(s, 0, i); // This is a strong invariant, but WP may struggle
                                                              // with the connection to max_freq_rec.
                                                              // A simpler max_frequency invariant is usually sufficient:
      loop invariant \for_all integer k; 0 <= k < i ==> max_frequency >= freq[k];
      loop invariant \for_all integer k; 0 <= k < 256 ==> freq[k] == char_count(s, (char)k); // Frequencies are final after first loop
      loop assigns max_frequency;
      loop variant 256 - i;
    */
    for (int i = 0; i < 256; i++) {
        if (freq[i] > max_frequency) {
            max_frequency = freq[i];
        }
    }

    // Check the condition: max_freq <= (len + 1) / 2
    if (max_frequency <= (len + 1) / 2) {
        return 1; // True
    } else {
        return 0; // False
    }
}
