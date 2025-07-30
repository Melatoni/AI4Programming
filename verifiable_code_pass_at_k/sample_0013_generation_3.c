// Task ID: 13
// Generation: 3

/*@
  // Rule I.1: No standard libraries. ACSL constants are implicitly available.

  // Rule II.1, II.2: Recursive logic for complexity.
  // Define an axiomatic block for properties related to words and counts.
  axiomatic WordCounts {
    logic integer count_occurrences{L}(int* words, int num_words, int word_idx) reads words[0..num_words-1];

    // Base case: If no words, count is 0.
    axiom count_occurrences_base_empty:
      \forall int* words, int num_words, int word_idx;
        num_words == 0 ==> count_occurrences(words, num_words, word_idx) == 0;

    // Base case: If word_idx is out of bounds, count is 0.
    axiom count_occurrences_base_out_of_bounds:
      \forall int* words, int num_words, int word_idx;
        word_idx < 0 || word_idx >= num_words ==> count_occurrences(words, num_words, word_idx) == 0;

    // Recursive step: Count occurrences of words[word_idx] in the array.
    axiom count_occurrences_recursive:
      \forall int* words, int num_words, int word_idx;
        0 <= word_idx < num_words ==>
          count_occurrences(words, num_words, word_idx) ==
          (\sum integer k; 0 <= k < num_words && words[k] == words[word_idx]; 1);

    // Helper axiom (Rule II.2): If all words are distinct, count is 1 for each.
    axiom count_occurrences_helper_distinct:
      \forall int* words, int num_words, int word_idx;
        (
          \forall integer i, j; 0 <= i < j < num_words ==> words[i] != words[j]
        ) ==> (
          count_occurrences(words, num_words, word_idx) == 1
        );

    // Helper axiom (Rule II.2): Max count is num_words.
    axiom count_occurrences_helper_max_count:
      \forall int* words, int num_words, int word_idx;
        count_occurrences(words, num_words, word_idx) <= num_words;

    // Helper axiom (Rule II.2): Count is non-negative.
    axiom count_occurrences_helper_non_negative:
      \forall int* words, int num_words, int word_idx;
        count_occurrences(words, num_words, word_idx) >= 0;

    logic integer max_count{L}(int* words, int num_words) reads words[0..num_words-1];

    // Base case: If no words, max count is 0.
    axiom max_count_base_empty:
      \forall int* words, int num_words;
        num_words == 0 ==> max_count(words, num_words) == 0;

    // Recursive step: Max count is the maximum of all individual word counts.
    axiom max_count_recursive:
      \forall int* words, int num_words;
        num_words > 0 ==>
          max_count(words, num_words) ==
          \max integer k; 0 <= k < num_words; count_occurrences(words, num_words, k);

    // Helper axiom (Rule II.2): Max count is non-negative.
    axiom max_count_helper_non_negative:
      \forall int* words, int num_words;
        max_count(words, num_words) >= 0;

    // Helper axiom (Rule II.2): Max count is at most num_words.
    axiom max_count_helper_upper_bound:
      \forall int* words, int num_words;
        max_count(words, num_words) <= num_words;
  }
*/

/*@
  requires num_words >= 0;
  // Rule II.5: Prevent potential out-of-bounds access if words is NULL and num_words > 0.
  // If num_words is 0, words can be NULL.
  requires num_words == 0 || \valid_read(words + (0..num_words-1));

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like functions.
  // The function returns the maximum count.
  ensures \result == max_count(words, num_words);
*/
int count_most_common_words(int* words, int num_words) {
    if (num_words == 0) {
        return 0;
    }

    int max_freq = 0;

    /*@
      loop invariant 0 <= i <= num_words;
      loop invariant max_freq == (\max integer k; 0 <= k < i; count_occurrences(words, num_words, k));
      loop invariant max_freq >= 0; // Rule II.2: Helper invariant
      loop invariant max_freq <= num_words; // Rule II.2: Helper invariant
      loop assigns i, max_freq;
      loop variant num_words - i;
    */
    for (int i = 0; i < num_words; i++) {
        int current_word = words[i];
        int current_freq = 0;

        /*@
          loop invariant 0 <= j <= num_words;
          loop invariant current_freq == (\sum integer k; 0 <= k < j && words[k] == current_word; 1);
          loop invariant current_freq <= num_words; // Rule II.2: Helper invariant
          loop invariant current_freq >= 0; // Rule II.2: Helper invariant
          loop assigns j, current_freq;
          loop variant num_words - j;
        */
        for (int j = 0; j < num_words; j++) {
            if (words[j] == current_word) {
                current_freq++;
            }
        }

        // Rule III.1: No C-style ternary in ACSL.
        // Rule III.2: No parentheses around if-then-else.
        if (current_freq > max_freq) {
            max_freq = current_freq;
        }
    }

    return max_freq;
}
