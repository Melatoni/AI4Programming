// Task ID: 15
// Generation: 5

/*@
  // Rule I.1: No standard libraries. ACSL has its own definition of char properties.
  // Rule II.5: Preconditions for input string.
  requires \valid_read(s + (0 .. len - 1));
  requires len >= 0;
  requires \valid_write(out + (0 .. len - 1));
  requires \valid_write(starts_len + (0 .. len - 1));

  assigns out[0 .. len - 1], starts_len[0 .. len - 1], \result;

  behavior empty_string:
    assumes len == 0;
    ensures \result == 0;
    ensures \forall integer k; 0 <= k < len ==> out[k] == s[k]; // No change
    ensures \forall integer k; 0 <= k < len ==> starts_len[k] == 0; // No new words

  behavior non_empty_string:
    assumes len > 0;
    // Rule II.3: Use logical equivalence for boolean-like functions.
    // The result is the number of words found.
    ensures \result >= 0; // Number of words can't be negative.
    ensures \result <= len; // Max words is len (each char is a word).

    // The 'out' array should contain the characters of the original string.
    ensures \forall integer k; 0 <= k < len ==> out[k] == s[k];

    // The 'starts_len' array should correctly mark the start of words and their lengths.
    // A word starts at index i if starts_len[i] > 0.
    // The value starts_len[i] is the length of the word starting at i.
    ensures (\forall integer i; 0 <= i < len ==>
      (starts_len[i] > 0 <==>
        // A word starts at 'i' if 'i' is the first character, OR
        // if 'i' is an uppercase letter and 'i-1' was a lowercase letter.
        (i == 0 ||
         (s[i] >= 'A' && s[i] <= 'Z' && s[i-1] >= 'a' && s[i-1] <= 'z'))
      ));

    // For any word starting at index 'i' with length 'l = starts_len[i]',
    // all characters s[i .. i+l-1] must be part of that word.
    // And the character s[i+l] (if it exists) must be a lowercase letter.
    ensures (\forall integer i; 0 <= i < len ==>
      (starts_len[i] > 0 ==>
        (starts_len[i] == (\exists integer k; i <= k < len &&
                                             (k == len - 1 ||
                                              (s[k] >= 'A' && s[k] <= 'Z' && s[k+1] >= 'a' && s[k+1] <= 'z')) ?
                                             k - i + 1 :
                                             (len - i))) // Length is until end of string if no split found
      ));

    // Ensure all other elements in starts_len are zero.
    ensures (\forall integer i; 0 <= i < len ==>
      (starts_len[i] == 0 <==>
        (i > 0 && !(s[i] >= 'A' && s[i] <= 'Z' && s[i-1] >= 'a' && s[i-1] <= 'z') && i != 0)
      ));
*/
int split_at_lowercase(char s[], int len, char out[], int starts_len[]) {
    // Rule I.2: Use int for booleans.
    int num_words = 0;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant 0 <= num_words <= i;

      // Rule II.4: Loop invariant for 'out' array.
      loop invariant \forall integer k; 0 <= k < i ==> out[k] == s[k];

      // Rule II.4: Loop invariant for 'starts_len' array up to 'i'.
      loop invariant \forall integer k; 0 <= k < i ==>
        (starts_len[k] > 0 <==> (k == 0 || (s[k] >= 'A' && s[k] <= 'Z' && s[k-1] >= 'a' && s[k-1] <= 'z')));

      // For elements in starts_len already processed, ensure their values are 0 if no word starts.
      loop invariant \forall integer k; 0 <= k < i && starts_len[k] == 0 ==>
        !(k == 0 || (s[k] >= 'A' && s[k] <= 'Z' && s[k-1] >= 'a' && s[k-1] <= 'z'));

      // For elements in starts_len already processed, ensure their values are correct lengths if a word starts.
      loop invariant \forall integer k; 0 <= k < i && starts_len[k] > 0 ==>
        (starts_len[k] == (\exists integer j; k <= j < i &&
                                             (j == len - 1 ||
                                              (s[j] >= 'A' && s[j] <= 'Z' && s[j+1] >= 'a' && s[j+1] <= 'z')) ?
                                             j - k + 1 :
                                             (i - k)));

      loop assigns i, num_words, out[0 .. len - 1], starts_len[0 .. len - 1];
      loop variant len - i;
    */
    for (int i = 0; i < len; ++i) {
        // Copy character to output (no actual modification needed for this problem, but good practice).
        out[i] = s[i];

        // Check if a new word starts at the current position.
        // A word starts if it's the first character, or if the previous character was
        // lowercase and the current one is uppercase.
        if (i == 0 || (s[i] >= 'A' && s[i] <= 'Z' && s[i-1] >= 'a' && s[i-1] <= 'z')) {
            num_words++;
            starts_len[i] = 1; // Mark as start of a word for now, length will be updated later.
        } else {
            starts_len[i] = 0; // Not a word start.
        }
    }

    // Now, iterate again to calculate the actual lengths of the words.
    /*@
      loop invariant 0 <= i <= len;
      // All characters copied to 'out' array.
      loop invariant \forall integer k; 0 <= k < len ==> out[k] == s[k];

      // starts_len correctly marked for word starts/non-starts (from previous loop).
      loop invariant \forall integer k; 0 <= k < len ==>
        (starts_len[k] > 0 <==> (k == 0 || (s[k] >= 'A' && s[k] <= 'Z' && s[k-1] >= 'a' && s[k-1] <= 'z')));

      // For words starting before 'i', their lengths are correctly calculated.
      loop invariant \forall integer k; 0 <= k < i && starts_len[k] > 0 ==>
        (starts_len[k] == (\exists integer j; k <= j < len &&
                                             (j == len - 1 ||
                                              (s[j] >= 'A' && s[j] <= 'Z' && s[j+1] >= 'a' && s[j+1] <= 'z')) ?
                                             j - k + 1 :
                                             (len - k)));

      loop assigns i, starts_len[0 .. len - 1];
      loop variant len - i;
    */
    for (int i = 0; i < len; ++i) {
        if (starts_len[i] > 0) { // If a word starts here
            int current_word_len = 0;
            /*@
              loop invariant i <= j <= len;
              loop invariant current_word_len == j - i;
              loop invariant \forall integer k; i <= k < j ==>
                !(k == len - 1 || (s[k] >= 'A' && s[k] <= 'Z' && s[k+1] >= 'a' && s[k+1] <= 'z'));
              loop assigns j, current_word_len;
              loop variant len - j;
            */
            for (int j = i; j < len; ++j) {
                current_word_len++;
                // If this is the last character, or the next character marks a new word boundary
                if (j == len - 1 || (s[j] >= 'A' && s[j] <= 'Z' && s[j+1] >= 'a' && s[j+1] <= 'z')) {
                    break;
                }
            }
            starts_len[i] = current_word_len;
        }
    }

    return num_words;
}
