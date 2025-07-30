// Task ID: 39
// Generation: 0

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This logic function checks if a string 's' of length 'len' has adjacent identical characters.
  axiomatic HasAdjacentIdentical {
    logic boolean has_adjacent_identical_char_rec(char *s, int len, int index);

    // Rule II.1: Base case for recursion.
    axiom has_adjacent_identical_char_rec_base:
      \forall char *s, int len;
        has_adjacent_identical_char_rec(s, len, len - 1) == \false;

    // Rule II.1: Recursive step.
    axiom has_adjacent_identical_char_rec_step:
      \forall char *s, int len, int index;
        0 <= index < len - 1 ==>
        (has_adjacent_identical_char_rec(s, len, index) ==
         (s[index] == s[index+1] || has_adjacent_identical_char_rec(s, len, index + 1)));

    // Helper logic function to check if any adjacent characters are identical in the whole string.
    logic boolean has_adjacent_identical_char(char *s, int len) =
      has_adjacent_identical_char_rec(s, len, 0);

    // Rule II.2: Helper axiom: if has_adjacent_identical_char is false, then no adjacent chars are identical.
    axiom has_adjacent_identical_char_false_property:
      \forall char *s, int len;
        has_adjacent_identical_char(s, len) == \false ==>
        (\forall integer i; 0 <= i < len - 1 ==> s[i] != s[i+1]);

    // Helper logic function to count character occurrences.
    logic integer count_char(char *s, int len, char c);

    // Rule II.1: Base case for count_char.
    axiom count_char_base:
      \forall char *s, char c;
        count_char(s, 0, c) == 0;

    // Rule II.1: Recursive step for count_char.
    axiom count_char_step:
      \forall char *s, int len, char c;
        len > 0 ==>
        (count_char(s, len, c) ==
         (if s[len-1] == c then 1 else 0) + count_char(s, len-1, c));

    // Rule II.2: Helper axiom: count_char is non-negative.
    axiom count_char_non_negative:
      \forall char *s, int len, char c;
        count_char(s, len, c) >= 0;
  }
*/

/*@
  requires len >= 0;
  // Rule II.5: Input string must be null-terminated if len > 0 for safety,
  // though not strictly required by the problem statement for arbitrary char arrays.
  // For simplicity, we assume s points to a valid char array of size len.
  // requires \valid_read(s + (0..len-1));

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function returns 1 if the string can be rearranged such that no two adjacent characters are the same.
  // This is equivalent to checking if the count of the most frequent character is not greater than
  // (len + 1) / 2.
  ensures (\exists char *rearranged_s;
            \fresh(rearranged_s, len) && // rearranged_s is a fresh memory block of size len
            \forall integer i; 0 <= i < len ==> count_char(s, len, s[i]) == count_char(rearranged_s, len, s[i]) && // Same character counts
            has_adjacent_identical_char(rearranged_s, len) == \false // No adjacent identical characters
          ) <==> (\result == 1);
*/
int can_rearrange_no_adjacent_same(char *s, int len) {
    // Determine the maximum frequency of any character.
    // ASCII characters (0-127)
    int freq[128] = {0}; // Rule I.1: No <limits.h>, so use a fixed size.

    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i ==> freq[s[k]] == count_char(s, i, s[k]);
      loop assigns i, freq;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Rule II.5: Ensure s[i] is a valid index for freq array.
        // Assuming ASCII characters, 0-127.
        /*@ requires 0 <= s[i] < 128; */
        freq[(int)s[i]]++;
    }

    int max_freq = 0;

    /*@
      loop invariant 0 <= i <= 128;
      loop invariant \forall integer k; 0 <= k < i ==> max_freq >= freq[k];
      loop assigns i, max_freq;
      loop variant 128 - i;
    */
    for (int i = 0; i < 128; i++) {
        if (freq[i] > max_freq) {
            max_freq = freq[i];
        }
    }

    // The condition for rearrangement is that the most frequent character's count
    // must not exceed (len + 1) / 2.
    // Rule I.2: Use int for boolean result.
    return max_freq <= (len + 1) / 2;
}
