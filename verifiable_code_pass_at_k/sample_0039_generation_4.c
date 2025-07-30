// Task ID: 39
// Generation: 4

/*@
  // Rule I.1: No standard libraries. ACSL built-in constants can be used if needed.

  // Rule II.1, II.2: Define a recursive logic function to check if a character
  // is present in a string. This avoids using standard library functions.
  axiomatic CharPresence {
    logic boolean char_in_string(char c, char *s, integer len);

    axiom char_in_string_base:
      \forall char c, char *s; char_in_string(c, s, 0) == \false;

    axiom char_in_string_recursive:
      \forall char c, char *s, integer len;
        len > 0 ==> (char_in_string(c, s, len) == (s[len - 1] == c || char_in_string(c, s, len - 1)));
  }

  // Rule II.1, II.2: Define a recursive logic function to count character occurrences.
  // This is crucial for checking the frequency condition later.
  axiomatic CharCount {
    logic integer count_char_in_string(char c, char *s, integer len);

    axiom count_char_in_string_base:
      \forall char c, char *s; count_char_in_string(c, s, 0) == 0;

    axiom count_char_in_string_recursive:
      \forall char c, char *s, integer len;
        len > 0 ==> (count_char_in_string(c, s, len) == (count_char_in_string(c, s, len - 1) + (s[len - 1] == c ? 1 : 0)));
  }

  // Rule II.1, II.2: Define a recursive logic function to find the maximum character count.
  axiomatic MaxCharCount {
    logic integer max_count(char *s, integer len);

    axiom max_count_base:
      \forall char *s; max_count(s, 0) == 0;

    axiom max_count_recursive:
      \forall char *s, integer len;
        len > 0 ==> (max_count(s, len) == \max(count_char_in_string(s[len-1], s, len), max_count(s, len - 1)));
  }

  // Helper axiom for max_count to handle cases where the string might be empty or contain
  // only unique characters.
  // Rule II.2: Crucial helper axioms to prove properties.
  axiomatic MaxCountHelperAxioms {
    // If len > 0, max_count is at least 1 if any char is present.
    // This axiom helps the prover understand the lower bound of max_count.
    axiom max_count_positive_if_not_empty:
      \forall char *s, integer len;
        len > 0 ==> max_count(s, len) >= 1;

    // The max count cannot exceed the total length of the string.
    axiom max_count_le_len:
      \forall char *s, integer len;
        max_count(s, len) <= len;
  }
*/

/*@
  requires \valid_read_string(s);
  requires len >= 0;
  // Rule II.5: Prevent potential overflow if len is very large, though for string
  // lengths, this is less likely to be an issue in practice.
  // The condition for rearrangement is max_freq <= (len + 1) / 2.
  // If len is close to INT_MAX, (len + 1) / 2 might overflow if not handled carefully,
  // but here we are comparing with max_count, which is also <= len.
  // So, the comparison itself is safe.
  // No specific overflow check for len is strictly necessary here given the problem
  // constraints on character counts.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // A string can be rearranged such that adjacent characters are different
  // if and only if the count of the most frequent character is not more than
  // (total_length + 1) / 2.
  ensures (\forall integer k; 0 <= k < len ==> max_count(s, len) <= (len + 1) / 2) <==> (\result == 1);
*/
int can_rearrange_adjacent_different(char *s, int len) { // Rule I.2: Uses int for boolean.
    // Base case: An empty string or a string with one character can always be rearranged.
    // They trivially satisfy the condition as there are no adjacent characters.
    if (len <= 1) {
        return 1;
    }

    // Array to store character counts. Assuming ASCII characters (0-255).
    // Rule I.1: No standard libraries, so we use a fixed-size array.
    int counts[256] = {0}; // Initialize all counts to 0.

    // Calculate character frequencies.
    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < 256 ==> counts[k] == count_char_in_string((char)k, s, i);
      loop assigns i, counts[0..255];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Rule II.5: Ensure s[i] is a valid index for counts.
        // This is implicitly covered by `\valid_read_string(s)` and char range 0-255.
        counts[(unsigned char)s[i]]++;
    }

    // Find the maximum frequency.
    int max_freq = 0;
    /*@
      loop invariant 0 <= i <= 256;
      loop invariant \forall integer k; 0 <= k < i ==> max_freq >= counts[k];
      loop invariant max_freq == (\max integer k_prime; 0 <= k_prime < i ? counts[k_prime] : 0);
      loop assigns i, max_freq;
      loop variant 256 - i;
    */
    for (int i = 0; i < 256; i++) {
        if (counts[i] > max_freq) {
            max_freq = counts[i];
        }
    }

    // The condition for rearrangement is max_freq <= (len + 1) / 2.
    // Rule I.2: Return 1 for true, 0 for false.
    if (max_freq <= (len + 1) / 2) {
        return 1;
    } else {
        return 0;
    }
}
