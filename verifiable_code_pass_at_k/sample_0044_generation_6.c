// Task ID: 44
// Generation: 6

/*@
  // Rule I.2: Use int for boolean return type.
  // Rule II.5: Prevent potential out-of-bounds access.
  requires \valid_read(text + (0..text_len - 1));
  requires \valid_read(word + (0..word_len - 1));
  requires text_len >= 0;
  requires word_len >= 0;

  // Rule II.3: Use logical equivalence for boolean-like functions.
  // The function returns 1 if the word matches the beginning of the text, 0 otherwise.
  ensures (\result == 1) <==>
          (word_len <= text_len &&
           (\forall integer k; 0 <= k < word_len ==> text[k] == word[k]));
  ensures (\result == 0) <==>
          !(word_len <= text_len &&
            (\forall integer k; 0 <= k < word_len ==> text[k] == word[k]));

  assigns \nothing;
*/
int match_word_at_beginning(char *text, int text_len, char *word, int word_len) {
    // If the word is longer than the text, it cannot possibly match.
    if (word_len > text_len) {
        return 0; // Rule I.2: Return 0 for false.
    }

    /*@
      loop invariant 0 <= i <= word_len;
      // If the loop reaches index i, all characters from 0 to i-1 must have matched.
      loop invariant \forall integer k; 0 <= k < i ==> text[k] == word[k];
      loop assigns i;
      loop variant word_len - i;
    */
    for (int i = 0; i < word_len; i++) {
        if (text[i] != word[i]) {
            return 0; // Rule I.2: Return 0 for false.
        }
    }

    // If the loop completes, all characters of word matched the beginning of text.
    return 1; // Rule I.2: Return 1 for true.
}
