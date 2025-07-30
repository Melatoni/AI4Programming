// Task ID: 30
// Generation: 3

/*@
  // Axiomatic block for recursive logic and helper axioms (Rule II.1, II.2).
  axiomatic SubstringCount {
    logic integer count_char_occurrences(char_array s, integer len, char c);
    
    // Base case: If length is 0, count is 0.
    axiom count_char_occurrences_base:
      \forall char_array s, char c;
        count_char_occurrences(s, 0, c) == 0;

    // Recursive case: If current char matches, add 1 to count, else add 0.
    axiom count_char_occurrences_recursive:
      \forall char_array s, integer len, char c;
        len > 0 ==> count_char_occurrences(s, len, c) ==
          (if s.content[len - 1] == c then 1 else 0) + count_char_occurrences(s, len - 1, c);

    // Helper axiom: If a char appears 'k' times, the number of substrings
    // starting and ending with that char is k * (k + 1) / 2.
    // This is the sum of integers from 1 to k.
    axiom sum_of_k_occurrences:
      \forall integer k; k >= 0 ==> k * (k + 1) / 2 == \sum(integer i; 1 <= i <= k, i);

    // Helper axiom: The total count is the sum of counts for each character.
    logic integer total_substrings_same_char(char_array s, integer len);

    axiom total_substrings_same_char_def:
      \forall char_array s, integer len;
        total_substrings_same_char(s, len) ==
          (if len == 0 then 0
           else
             (if len == 1 then 1
              else
                (count_char_occurrences(s, len, 'a') * (count_char_occurrences(s, len, 'a') + 1) / 2) +
                (count_char_occurrences(s, len, 'b') * (count_char_occurrences(s, len, 'b') + 1) / 2) +
                (count_char_occurrences(s, len, 'c') * (count_char_occurrences(s, len, 'c') + 1) / 2) +
                (count_char_occurrences(s, len, 'd') * (count_char_occurrences(s, len, 'd') + 1) / 2) +
                (count_char_occurrences(s, len, 'e') * (count_char_occurrences(s, len, 'e') + 1) / 2) +
                (count_char_occurrences(s, len, 'f') * (count_char_occurrences(s, len, 'f') + 1) / 2) +
                (count_char_occurrences(s, len, 'g') * (count_char_occurrences(s, len, 'g') + 1) / 2) +
                (count_char_occurrences(s, len, 'h') * (count_char_occurrences(s, len, 'h') + 1) / 2) +
                (count_char_occurrences(s, len, 'i') * (count_char_occurrences(s, len, 'i') + 1) / 2) +
                (count_char_occurrences(s, len, 'j') * (count_char_occurrences(s, len, 'j') + 1) / 2) +
                (count_char_occurrences(s, len, 'k') * (count_char_occurrences(s, len, 'k') + 1) / 2) +
                (count_char_occurrences(s, len, 'l') * (count_char_occurrences(s, len, 'l') + 1) / 2) +
                (count_char_occurrences(s, len, 'm') * (count_char_occurrences(s, len, 'm') + 1) / 2) +
                (count_char_occurrences(s, len, 'n') * (count_char_occurrences(s, len, 'n') + 1) / 2) +
                (count_char_occurrences(s, len, 'o') * (count_char_occurrences(s, len, 'o') + 1) / 2) +
                (count_char_occurrences(s, len, 'p') * (count_char_occurrences(s, len, 'p') + 1) / 2) +
                (count_char_occurrences(s, len, 'q') * (count_char_occurrences(s, len, 'q') + 1) / 2) +
                (count_char_occurrences(s, len, 'r') * (count_char_occurrences(s, len, 'r') + 1) / 2) +
                (count_char_occurrences(s, len, 's') * (count_char_occurrences(s, len, 's') + 1) / 2) +
                (count_char_occurrences(s, len, 't') * (count_char_occurrences(s, len, 't') + 1) / 2) +
                (count_char_occurrences(s, len, 'u') * (count_char_occurrences(s, len, 'u') + 1) / 2) +
                (count_char_occurrences(s, len, 'v') * (count_char_occurrences(s, len, 'v') + 1) / 2) +
                (count_char_occurrences(s, len, 'w') * (count_char_occurrences(s, len, 'w') + 1) / 2) +
                (count_char_occurrences(s, len, 'x') * (count_char_occurrences(s, len, 'x') + 1) / 2) +
                (count_char_occurrences(s, len, 'y') * (count_char_occurrences(s, len, 'y') + 1) / 2) +
                (count_char_occurrences(s, len, 'z') * (count_char_occurrences(s, len, 'z') + 1) / 2)
             )
          );
  }
*/

/*@
  requires length >= 0;
  requires \valid_read_range(s, 0, length - 1);
  // Prevent overflow for count * (count + 1) / 2
  // Max possible count is length. Max length for int is around INT_MAX.
  // INT_MAX * (INT_MAX + 1) / 2 requires a 64-bit integer, but we return int.
  // So, we must constrain length such that length * (length + 1) / 2 does not overflow int.
  // Max length for int (2^31-1) is sqrt(2*INT_MAX) approx 65535.
  // Assuming a 32-bit int, INT_MAX = 2147483647.
  // Max length where length * (length + 1) / 2 <= INT_MAX is approx 65535.
  // We use a slightly smaller bound to be safe and account for summing multiple such values.
  requires length <= 46340; // Max length where length*(length+1)/2 fits in int (46340 * 46341 / 2 = 1073760470)

  assigns \nothing;

  ensures \result == total_substrings_same_char(\array_shift(s, 0), length);
*/
int count_substrings_same_char(char *s, int length) {
    if (length == 0) {
        return 0;
    }

    // Array to store counts of each character 'a' through 'z'
    // There are 26 characters in the English alphabet.
    /*@
      requires \valid(char_counts + (0..25));
      assigns char_counts[0..25];
      loop invariant \forall integer k; 0 <= k < 26 ==> char_counts[k] == 0;
      loop variant 26 - i;
    */
    int char_counts[26];
    for (int i = 0; i < 26; i++) {
        char_counts[i] = 0;
    }

    /*@
      loop invariant 0 <= i <= length;
      loop invariant \forall integer k; 0 <= k < 26 ==> char_counts[k] == count_char_occurrences(\array_shift(s,0), i, (char)('a' + k));
      loop assigns char_counts[0..25], i;
      loop variant length - i;
    */
    for (int i = 0; i < length; i++) {
        // Only consider lowercase English letters for simplicity as per common problem constraints.
        // If other characters are expected, the char_counts array size and indexing would need adjustment.
        /*@
          requires 'a' <= s[i] <= 'z'; // Assume input string only contains lowercase English letters
          assigns char_counts[s[i] - 'a'];
        */
        char_counts[s[i] - 'a']++;
    }

    int total_count = 0;
    /*@
      loop invariant 0 <= i <= 26;
      loop invariant total_count == \sum(integer k; 0 <= k < i, char_counts[k] * (char_counts[k] + 1) / 2);
      loop assigns total_count, i;
      loop variant 26 - i;
    */
    for (int i = 0; i < 26; i++) {
        int count = char_counts[i];
        // The number of substrings starting and ending with the same character
        // for a character that appears 'count' times is count * (count + 1) / 2.
        // This is the sum of integers from 1 to 'count'.
        /*@
          requires count >= 0;
          // Ensure count * (count + 1) / 2 does not overflow.
          // Max count is 'length', which is already constrained by function's requires clause.
          requires count <= 46340;
          assigns total_count;
        */
        total_count += count * (count + 1) / 2;
    }

    return total_count;
}
