// Task ID: 30
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define a recursive logic function for counting substrings.
  // This function counts substrings starting and ending with the same character
  // within a given range [low, high).
  axiomatic SubstringCount {
    logic integer count_same_char_substr(char* s, integer low, integer high, integer len);

    // Base case: If the range is empty or contains a single character,
    // the count is just the number of single characters (which is high - low).
    // A single character is considered a substring starting and ending with itself.
    axiom count_same_char_substr_base:
      \forall char* s, integer low, integer high, integer len;
        low >= high ==> count_same_char_substr(s, low, high, len) == 0;

    axiom count_same_char_substr_single:
      \forall char* s, integer low, integer high, integer len;
        low + 1 == high ==> count_same_char_substr(s, low, high, len) == 1;

    // Recursive case:
    // The count for [low, high) is the count for [low+1, high)
    // plus the number of substrings starting at 'low' and ending with s[low].
    axiom count_same_char_substr_recursive:
      \forall char* s, integer low, integer high, integer len;
        low < high - 1 ==>
          count_same_char_substr(s, low, high, len) ==
          count_same_char_substr(s, low + 1, high, len) +
          (1 + // The single character s[low] itself
           (\sum integer k; low + 1 <= k < high && s[low] == s[k]; 1)
          );
  }
*/

/*@
  requires \valid_read(s + (0..len - 1));
  requires len >= 0;
  // Rule II.5: Prevent potential overflow if len is very large, though the sum itself
  // can grow quadratically. For a string of length N, the maximum count is N*(N+1)/2.
  // For int, N*(N+1)/2 <= INT_MAX => N approx 65535.
  // Assuming len is within reasonable bounds for int return value.
  // For example, if len is max 32767, then 32767*32768/2 = 536854528, which fits in int.
  requires len <= 65535; // Maximum len for result to fit in a 32-bit signed int.

  assigns \nothing;

  ensures \result == count_same_char_substr(s, 0, len, len);
*/
int count_same_char_substrings(char* s, int len) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant count == count_same_char_substr(s, 0, i, len);
      loop assigns count, i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Each single character is a substring starting and ending with itself.
        count++;

        /*@
          loop invariant i + 1 <= j <= len;
          loop invariant count == count_same_char_substr(s, 0, i, len) + 1 +
                           (\sum integer k; i + 1 <= k < j && s[i] == s[k]; 1);
          loop assigns count, j;
          loop variant len - j;
        */
        for (int j = i + 1; j < len; j++) {
            if (s[i] == s[j]) {
                count++;
            }
        }
    }
    return count;
}
