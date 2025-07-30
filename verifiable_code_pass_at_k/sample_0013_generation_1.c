// Task ID: 13
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Define maximum lengths for words and dictionary size for safety and verifiability.
  // These constants are used to bound array sizes and loop iterations.
  #define MAX_WORD_LEN 32
  #define MAX_DICT_SIZE 1000

  // Axiomatic block for recursive logic and helper functions.
  axiomatic WordCount {

    // Helper logic function to check if two words are equal.
    // This is crucial for comparing strings (char arrays).
    logic int word_equal_at(char* w1, char* w2, int len, int k) reads w1, w2;

    axiom word_equal_at_base:
      \forall char* w1, char* w2, int len;
        0 <= len ==> word_equal_at(w1, w2, len, len) == 1; // Empty prefix is always equal (base case)

    axiom word_equal_at_rec:
      \forall char* w1, char* w2, int len, int k;
        0 <= k < len ==> (word_equal_at(w1, w2, len, k) == (if w1[k] == w2[k] then word_equal_at(w1, w2, len, k + 1) else 0));

    // A wrapper for word_equal_at to check full word equality.
    // Returns 1 if words are equal, 0 otherwise.
    logic int word_equal(char* w1, char* w2, int len) = word_equal_at(w1, w2, len, 0);

    // Helper logic function to count occurrences of a specific word up to a given index.
    logic integer count_word_occurrences_up_to(char words[][MAX_WORD_LEN], int dict_size, int word_len, char* target_word, int k) reads words;

    axiom count_word_occurrences_up_to_base:
      \forall char words[][MAX_WORD_LEN], int dict_size, int word_len, char* target_word;
        count_word_occurrences_up_to(words, dict_size, word_len, target_word, 0) == 0;

    axiom count_word_occurrences_up_to_rec:
      \forall char words[][MAX_WORD_LEN], int dict_size, int word_len, char* target_word, int k;
        0 <= k < dict_size ==>
          (count_word_occurrences_up_to(words, dict_size, word_len, target_word, k + 1) ==
           (if word_equal(words[k], target_word, word_len) then count_word_occurrences_up_to(words, dict_size, word_len, target_word, k) + 1
            else count_word_occurrences_up_to(words, dict_size, word_len, target_word, k)));

    // Total occurrences of a word in the entire dictionary.
    logic integer total_word_occurrences(char words[][MAX_WORD_LEN], int dict_size, int word_len, char* target_word) =
      count_word_occurrences_up_to(words, dict_size, word_len, target_word, dict_size);

    // Helper logic function to find the maximum count among a subset of words.
    logic integer max_count_up_to(char words[][MAX_WORD_LEN], int dict_size, int word_len, int k) reads words;

    axiom max_count_up_to_base:
      \forall char words[][MAX_WORD_LEN], int dict_size, int word_len;
        max_count_up_to(words, dict_size, word_len, 0) == 0; // Or -1 if no words are considered yet

    axiom max_count_up_to_rec:
      \forall char words[][MAX_WORD_LEN], int dict_size, int word_len, int k;
        0 <= k < dict_size ==>
          (max_count_up_to(words, dict_size, word_len, k + 1) ==
           \max(max_count_up_to(words, dict_size, word_len, k), total_word_occurrences(words, dict_size, word_len, words[k])));

    // The maximum count of any word in the dictionary.
    logic integer overall_max_count(char words[][MAX_WORD_LEN], int dict_size, int word_len) =
      max_count_up_to(words, dict_size, word_len, dict_size);
  }
*/

/*@
  requires dict_size >= 0 && dict_size <= MAX_DICT_SIZE;
  requires word_len >= 0 && word_len <= MAX_WORD_LEN;
  // Ensure that all words in the dictionary are properly null-terminated within their length.
  // This helps prevent out-of-bounds reads when comparing words.
  requires \forall integer i; 0 <= i < dict_size ==> \valid_read(words[i] + (0..word_len));
  requires \forall integer i; 0 <= i < dict_size ==> words[i][word_len] == '\0';

  // Ensure the output buffer for the most common word is valid.
  requires \valid_write(most_common_word + (0..word_len));
  assigns *most_common_word, *most_common_word[0..word_len]; // Explicitly assign to the array contents.

  // The ensures clause uses logical equivalence.
  // The function returns the count of the most common word.
  // The word itself is copied into 'most_common_word'.
  ensures \result == overall_max_count(words, dict_size, word_len);

  // If dict_size is 0, the result should be 0 and most_common_word should be an empty string.
  ensures dict_size == 0 ==> \result == 0 && most_common_word[0] == '\0';

  // If dict_size > 0, then the word stored in most_common_word must indeed be one of the words
  // that achieves the overall_max_count.
  ensures dict_size > 0 ==>
    (total_word_occurrences(words, dict_size, word_len, most_common_word) == overall_max_count(words, dict_size, word_len));
*/
int count_most_common_words(
    char words[][MAX_WORD_LEN],
    int dict_size,
    int word_len,
    char most_common_word[MAX_WORD_LEN]
) {
    if (dict_size == 0) {
        most_common_word[0] = '\0'; // Empty string for no words.
        return 0;
    }

    int max_count = 0;
    // We assume the first word is the most common initially.
    // This is safe because dict_size > 0.

    /*@
      loop invariant 0 <= i <= dict_size;
      loop invariant 0 <= max_count;
      // max_count at iteration i is the maximum count found among words[0..i-1].
      loop invariant max_count == max_count_up_to(words, dict_size, word_len, i);

      // If max_count > 0, then most_common_word contains a word from words[0..i-1]
      // that has 'max_count' occurrences.
      loop invariant max_count > 0 ==>
        total_word_occurrences(words, dict_size, word_len, most_common_word) == max_count;

      loop assigns i, max_count, most_common_word[0..word_len];
      loop variant dict_size - i;
    */
    for (int i = 0; i < dict_size; i++) {
        int current_word_count = 0;
        char* current_word = words[i];

        /*@
          loop invariant 0 <= j <= dict_size;
          loop invariant current_word_count == count_word_occurrences_up_to(words, dict_size, word_len, current_word, j);
          loop assigns j, current_word_count;
          loop variant dict_size - j;
        */
        for (int j = 0; j < dict_size; j++) {
            // Compare current_word with words[j]
            int k = 0;
            int are_equal = 1; // boolean-like int

            /*@
              loop invariant 0 <= k <= word_len;
              loop invariant are_equal == word_equal_at(current_word, words[j], word_len, k);
              loop assigns k, are_equal;
              loop variant word_len - k;
            */
            while (k < word_len) {
                if (current_word[k] != words[j][k]) {
                    are_equal = 0;
                    break;
                }
                k++;
            }
            // Ensure null-terminator is also checked for full equality if word_len doesn't cover it.
            // This is implicitly handled if word_len is the true length and words are null-terminated.
            // For now, we assume word_len covers the significant part of the word.

            if (are_equal) {
                current_word_count++;
            }
        }

        if (current_word_count > max_count) {
            max_count = current_word_count;

            // Copy current_word to most_common_word
            /*@
              loop invariant 0 <= k <= word_len + 1; // +1 to copy null terminator
              loop invariant \forall integer m; 0 <= m < k ==> most_common_word[m] == current_word[m];
              loop assigns k, most_common_word[0..word_len];
              loop variant (word_len + 1) - k;
            */
            for (int k = 0; k <= word_len; k++) { // Copy including null terminator
                most_common_word[k] = current_word[k];
            }
        }
    }

    return max_count;
}
