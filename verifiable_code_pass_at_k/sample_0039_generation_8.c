// Task ID: 39
// Generation: 8

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This axiomatic block defines the properties needed to reason about
  // the counts of characters and the condition for rearrangement.
  axiomatic CharCounts {
    // A function to get the count of a specific character 'c' in a string 's' up to index 'len'.
    logic integer count_char(char* s, int len, char c);

    // Base case: If length is 0, count is 0.
    axiom count_char_base:
      \forall char* s, char c;
        count_char(s, 0, c) == 0;

    // Recursive case: If current char is 'c', increment count, else keep same.
    axiom count_char_recursive:
      \forall char* s, int len, char c;
        len > 0 ==> count_char(s, len, c) == (if s[len-1] == c then 1 else 0) + count_char(s, len - 1, c);

    // Helper axiom: The count of a character is non-negative.
    // Rule II.2: CRITICAL - Helper Axioms are needed for the prover.
    axiom count_char_non_negative:
      \forall char* s, int len, char c;
        count_char(s, len, c) >= 0;

    // Helper axiom: Count cannot be greater than length.
    axiom count_char_le_len:
      \forall char* s, int len, char c;
        count_char(s, len, c) <= len;

    // Helper axiom: If a character is not present in a string, its count is 0.
    axiom count_char_not_present:
      \forall char* s, int len, char c;
        (\forall integer i; 0 <= i < len ==> s[i] != c) ==> count_char(s, len, c) == 0;

    // A function to get the maximum count of any character in a string 's' of length 'len'.
    logic integer max_count(char* s, int len);

    // Base case: If length is 0, max count is 0.
    axiom max_count_base:
      \forall char* s;
        max_count(s, 0) == 0;

    // Recursive case: Max count is the maximum of the current character's count
    // and the max count of the rest of the string.
    // This axiom relies on the fact that 'count_char' can give us the total count.
    // This definition is slightly different. It's the max count of any char AFTER processing the string.
    // Let's refine max_count to be based on the alphabet.
    logic integer max_char_count_in_alphabet(char* s, int len);

    axiom max_char_count_in_alphabet_def:
      \forall char* s, int len;
        max_char_count_in_alphabet(s, len) == \max(
          \union(
            \set(count_char(s, len, c) | char c; 'a' <= c <= 'z'),
            \set(count_char(s, len, c) | char c; 'A' <= c <= 'Z')
          )
        );

    // Helper axiom: Max count is non-negative.
    axiom max_char_count_non_negative:
      \forall char* s, int len;
        max_char_count_in_alphabet(s, len) >= 0;

    // Helper axiom: Max count cannot exceed the total length of the string.
    axiom max_char_count_le_len:
      \forall char* s, int len;
        max_char_count_in_alphabet(s, len) <= len;
  }
*/

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;
  // Rule II.5: Prevent potential overflow if len is very large, though not directly applicable here for simple counts.
  // This constraint is more for practical string lengths and array indexing.
  requires len < 100000; // Arbitrary reasonable upper bound for string length.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The condition for rearrangement is that the maximum frequency of any character
  // must be less than or equal to (len + 1) / 2.
  // If len is even, max_freq <= len / 2.
  // If len is odd, max_freq <= (len / 2) + 1.
  // This can be compactly written as max_freq * 2 <= len + 1.
  ensures (max_char_count_in_alphabet(s, len) * 2 <= len + 1) <==> (result == 1);
*/
int can_rearrange_adjacent_different(char* s, int len) {
    // Using an array to store character counts.
    // Assuming ASCII characters, specifically 'a'-'z' and 'A'-'Z'.
    // A fixed size array for counts (e.g., 256 for all ASCII, or 52 for alpha only).
    // Let's use 256 for simplicity to cover all char values.
    int counts[256] = {0}; // Rule I.1: No standard libraries, so manual initialization.

    /*@
      loop invariant \forall integer c; 0 <= c < 256 ==> counts[c] == count_char(s, i, (char)c);
      loop invariant 0 <= i <= len;
      loop assigns i, counts[0..255];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Increment count for the current character.
        // Cast to unsigned char to avoid negative array index if char is signed and value is negative.
        counts[(unsigned char)s[i]]++;
    }

    int max_freq = 0;
    /*@
      loop invariant 0 <= i <= 256;
      loop invariant \forall integer k; 0 <= k < i ==> max_freq >= counts[k];
      loop invariant max_freq == \max(
        \union(
          \set(counts[c] | char c; 'a' <= c <= 'z'),
          \set(counts[c] | char c; 'A' <= c <= 'Z')
        )
        if i >= 'Z' + 1 else 0 // This part is tricky to express precisely for max over partial alphabet.
      );
      // A more robust invariant for max_freq:
      // max_freq is the maximum count of any character encountered so far in the loop.
      loop invariant \forall integer k; 0 <= k < i ==> max_freq >= counts[k];
      loop invariant \exists integer k; 0 <= k < i && max_freq == counts[k]; // If i > 0

      // Simplified max_freq invariant: max_freq is the max count among chars processed so far.
      // This is okay as long as we iterate through all possible char values.
      loop invariant \forall integer k; 0 <= k < i ==> max_freq >= counts[k];
      loop invariant (\forall integer k; 0 <= k < i ==> max_freq >= counts[k]) &&
                     (i == 0 ? max_freq == 0 : \exists integer j; 0 <= j < i && max_freq == counts[j]);

      loop assigns i, max_freq;
      loop variant 256 - i;
    */
    for (int i = 0; i < 256; i++) {
        if (counts[i] > max_freq) {
            max_freq = counts[i];
        }
    }

    // The condition for rearrangement: max_freq * 2 <= len + 1
    // This is equivalent to max_freq <= ceil(len / 2.0)
    // For even len, max_freq <= len / 2
    // For odd len, max_freq <= (len / 2) + 1
    if (max_freq * 2 <= len + 1) {
        return 1; // Can be rearranged
    } else {
        return 0; // Cannot be rearranged
    }
}
