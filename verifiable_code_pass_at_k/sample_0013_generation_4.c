// Task ID: 13
// Generation: 4

/*@
  // Rule I.1: No standard library includes.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Represents the number of occurrences of a specific word ID up to a given index.
  axiomatic WordCount {
    logic integer word_count_up_to(int word_id, int *words, int length, int idx);

    axiom word_count_up_to_base:
      \forall int word_id, int *words, int length;
        word_count_up_to(word_id, words, length, -1) == 0;

    axiom word_count_up_to_recursive:
      \forall int word_id, int *words, int length, int idx;
        0 <= idx < length ==>
          word_count_up_to(word_id, words, length, idx) ==
            word_count_up_to(word_id, words, length, idx - 1) +
            (if words[idx] == word_id then 1 else 0);

    // Rule II.2: Helper axiom to relate total count to count up to last element.
    axiom word_count_total:
      \forall int word_id, int *words, int length;
        0 <= length ==>
          word_count_up_to(word_id, words, length, length - 1) ==
            (\num_of(integer k; 0 <= k < length && words[k] == word_id));
  }
*/

/*@
  requires length >= 0;
  requires num_distinct_words >= 0;
  // Rule II.5: Prevent out-of-bounds access for words.
  requires \valid_read_range(words, 0, length - 1);
  // Rule II.5: Prevent out-of-bounds access for distinct_words.
  requires \valid_read_range(distinct_words, 0, num_distinct_words - 1);
  // Rule II.5: Prevent out-of-bounds access for counts.
  requires \valid_write_range(counts, 0, num_distinct_words - 1);

  assigns counts[0..num_distinct_words - 1];

  // Rule II.3: Ensures clause using logical equivalence.
  ensures \forall integer i; 0 <= i < num_distinct_words ==>
    counts[i] == (\num_of(integer k; 0 <= k < length && words[k] == distinct_words[i]));
*/
void count_word_occurrences(int *words, int length, int *distinct_words, int num_distinct_words, int *counts) {
    /*@
      loop invariant 0 <= i <= num_distinct_words;
      loop invariant \forall integer k; 0 <= k < i ==>
        counts[k] == (\num_of(integer l; 0 <= l < length && words[l] == distinct_words[k]));
      loop assigns i, counts[0..num_distinct_words - 1];
      loop variant num_distinct_words - i;
    */
    for (int i = 0; i < num_distinct_words; ++i) {
        int current_distinct_word_id = distinct_words[i];
        int current_count = 0;
        /*@
          loop invariant 0 <= j <= length;
          loop invariant current_count == (\num_of(integer k; 0 <= k < j && words[k] == current_distinct_word_id));
          loop assigns j, current_count;
          loop variant length - j;
        */
        for (int j = 0; j < length; ++j) {
            if (words[j] == current_distinct_word_id) {
                current_count++;
            }
        }
        counts[i] = current_count;
    }
}

/*@
  requires num_distinct_words >= 0;
  // Rule II.5: Prevent out-of-bounds access for distinct_words.
  requires \valid_read_range(distinct_words, 0, num_distinct_words - 1);
  // Rule II.5: Prevent out-of-bounds access for counts.
  requires \valid_read_range(counts, 0, num_distinct_words - 1);
  // Rule II.5: Prevent out-of-bounds access for most_common_word_id.
  requires \valid_write(most_common_word_id);
  // Rule II.5: Prevent out-of-bounds access for max_count.
  requires \valid_write(max_count);

  assigns *most_common_word_id, *max_count;

  behavior empty_array:
    assumes num_distinct_words == 0;
    assigns *most_common_word_id, *max_count;
    ensures *most_common_word_id == 0; // Or some other default, e.g., -1
    ensures *max_count == 0;

  behavior non_empty_array:
    assumes num_distinct_words > 0;
    assigns *most_common_word_id, *max_count;
    // Rule II.3: Ensures clause using logical equivalence.
    ensures \exists integer i; 0 <= i < num_distinct_words &&
      distinct_words[i] == *most_common_word_id &&
      counts[i] == *max_count &&
      (\forall integer j; 0 <= j < num_distinct_words ==> counts[j] <= *max_count);
*/
void find_most_common_word(int *distinct_words, int num_distinct_words, int *counts,
                            int *most_common_word_id, int *max_count) {
    if (num_distinct_words == 0) {
        *most_common_word_id = 0; // Rule I.2: Default value for 'no word'
        *max_count = 0;
        return;
    }

    *most_common_word_id = distinct_words[0];
    *max_count = counts[0];

    /*@
      loop invariant 0 <= i <= num_distinct_words;
      loop invariant 0 <= *max_count;
      loop invariant \exists integer k; 0 <= k < i && distinct_words[k] == *most_common_word_id && counts[k] == *max_count;
      loop invariant \forall integer k; 0 <= k < i ==> counts[k] <= *max_count;
      loop assigns i, *most_common_word_id, *max_count;
      loop variant num_distinct_words - i;
    */
    for (int i = 1; i < num_distinct_words; ++i) {
        if (counts[i] > *max_count) {
            *max_count = counts[i];
            *most_common_word_id = distinct_words[i];
        }
    }
}
