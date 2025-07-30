// Task ID: 13
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay (not applicable here, but kept in mind).
  // Rule II.1: Recursive logic for complexity (not directly applicable here, but kept in mind).
  // Rule II.2: Helper axioms (not directly applicable here, but kept in mind).
  // Rule II.5: Prevent Runtime Errors (RTE)

  // Maximum value for an integer, used for overflow checks.
  // This is a Frama-C built-in constant.
  // Note: INT_MAX is a macro in <limits.h>, but Frama-C's ACSL
  // directly knows about it as a constant for integer types.
  // For `int`, it's typically 2147483647.
  // For simplicity and to avoid specific platform dependencies,
  // we state a general upper bound that fits typical int sizes.
  // The problem implies a limited dictionary size and word length to avoid
  // extreme cases that would require 64-bit integers or more complex
  // memory management.
*/

/*@ axiomatic WordProperties {
  // Define a logic function to represent string equality.
  // C strings are null-terminated, so we need to compare characters
  // until a null terminator is found.
  // This logic function assumes valid C strings are passed, i.e.,
  // they are null-terminated within their allocated bounds.

  // Rule II.1: Recursive logic for complexity.
  logic boolean string_equal_at_idx(char *s1, char *s2, integer idx) =
    s1[idx] == '\0' && s2[idx] == '\0'
    || s1[idx] != '\0' && s2[idx] != '\0' && s1[idx] == s2[idx] && string_equal_at_idx(s1, s2, idx + 1);

  logic boolean string_equal(char *s1, char *s2) = string_equal_at_idx(s1, s2, 0);

  // Helper axiom for string equality: if strings are equal, their lengths are equal.
  // (Not strictly necessary for this problem, but good practice for completeness)
  // logic integer string_length_at_idx(char *s, integer idx) =
  //   s[idx] == '\0' ? idx : string_length_at_idx(s, idx + 1);
  // logic integer string_length(char *s) = string_length_at_idx(s, 0);

  // axiom string_equal_implies_equal_length:
  //   \forall char *s1, char *s2;
  //     string_equal(s1, s2) ==> string_length(s1) == string_length(s2);
}
*/

// Assume a maximum word length to avoid dynamic memory or complex string handling.
// This simplifies verification by making string comparisons bounded.
#define MAX_WORD_LEN 63 // Including null terminator, so 62 actual characters.

// Assume a maximum number of unique words in the dictionary.
#define MAX_DICT_SIZE 1000

// Structure to hold a word and its count.
struct WordCount {
    char word[MAX_WORD_LEN + 1]; // +1 for null terminator
    int count;
};

/*@
  requires \valid_read(word_list + (0..num_words-1));
  requires \forall integer i; 0 <= i < num_words ==> \valid_read_string(word_list[i]);
  requires \forall integer i; 0 <= i < num_words ==> \strlen(word_list[i]) <= MAX_WORD_LEN;
  requires num_words >= 0;
  requires unique_words_capacity >= 0;
  requires unique_words_capacity <= MAX_DICT_SIZE; // Constraint on capacity
  requires \valid(unique_words + (0..unique_words_capacity-1));
  requires \forall integer i; 0 <= i < unique_words_capacity ==> \valid(unique_words[i].word);
  requires \forall integer i; 0 <= i < unique_words_capacity ==> unique_words[i].count == 0; // Initial state

  assigns unique_words[0..unique_words_capacity-1];

  // The function computes the counts of words and returns the number of unique words found.
  // The unique_words array will be populated with words and their counts.
  // The first `\result` elements of unique_words will contain valid data.
  ensures 0 <= \result <= unique_words_capacity;
  ensures \forall integer i; 0 <= i < \result ==> unique_words[i].count > 0;
  ensures \forall integer i, j; 0 <= i < j < \result ==> !string_equal(unique_words[i].word, unique_words[j].word);

  // Ensure all words from word_list are accounted for in unique_words.
  // This is a strong post-condition, difficult to prove without helper functions.
  // A simpler post-condition might be:
  // ensures (\sum integer i; 0 <= i < \result; unique_words[i].count) == num_words;
  // Let's try to express the full accounting.
  ensures \forall integer i; 0 <= i < num_words ==>
    (\exists integer j; 0 <= j < \result && string_equal(word_list[i], unique_words[j].word));

  // Ensure that each unique word's count is correct.
  ensures \forall integer j; 0 <= j < \result ==>
    unique_words[j].count == (\num_of integer i; 0 <= i < num_words && string_equal(word_list[i], unique_words[j].word));
*/
int count_words(char *word_list[], int num_words, struct WordCount unique_words[], int unique_words_capacity) {
    int num_unique_found = 0;

    /*@
      loop invariant 0 <= i <= num_words;
      loop invariant 0 <= num_unique_found <= unique_words_capacity;
      loop invariant \forall integer k; 0 <= k < num_unique_found ==> unique_words[k].count > 0;
      loop invariant \forall integer k, l; 0 <= k < l < num_unique_found ==> !string_equal(unique_words[k].word, unique_words[l].word);

      // All words processed so far (word_list[0..i-1]) have been accounted for.
      loop invariant \forall integer k; 0 <= k < i ==>
        (\exists integer j; 0 <= j < num_unique_found && string_equal(word_list[k], unique_words[j].word));

      // Counts for unique words found so far are correct for word_list[0..i-1].
      loop invariant \forall integer j; 0 <= j < num_unique_found ==>
        unique_words[j].count == (\num_of integer k; 0 <= k < i && string_equal(word_list[k], unique_words[j].word));

      loop assigns i, num_unique_found, unique_words[0..unique_words_capacity-1];
      loop variant num_words - i;
    */
    for (int i = 0; i < num_words; i++) {
        char *current_word = word_list[i];
        int found = 0; // Rule I.2: Use int for boolean.

        /*@
          loop invariant 0 <= j <= num_unique_found;
          loop invariant found == 0 ==> (\forall integer k; 0 <= k < j ==> !string_equal(current_word, unique_words[k].word));
          loop invariant found == 1 ==> (\exists integer k; 0 <= k < j && string_equal(current_word, unique_words[k].word));
          loop invariant \forall integer k; 0 <= k < num_unique_found ==> unique_words[k].count > 0; // Preserve counts

          loop assigns j, found, unique_words[0..num_unique_found-1].count; // Only counts might change in this loop
          loop variant num_unique_found - j;
        */
        for (int j = 0; j < num_unique_found; j++) {
            // Compare current_word with unique_words[j].word
            // Manual string comparison to avoid standard library functions.
            int k = 0;
            // Rule II.5: Prevent overflow in k by bounding MAX_WORD_LEN.
            // Also, ensures valid memory access.
            /*@
              loop invariant 0 <= k <= MAX_WORD_LEN + 1;
              loop invariant \forall integer l; 0 <= l < k ==> current_word[l] == unique_words[j].word[l];
              loop assigns k;
              loop variant (MAX_WORD_LEN + 1) - k;
            */
            while (k <= MAX_WORD_LEN && current_word[k] != '\0' && unique_words[j].word[k] != '\0' && current_word[k] == unique_words[j].word[k]) {
                k++;
            }

            // Check if both strings ended at the same time and characters matched up to that point.
            if (current_word[k] == '\0' && unique_words[j].word[k] == '\0') {
                // Word found, increment count.
                // Rule II.5: Prevent count overflow. Assumes counts don't exceed INT_MAX.
                // Given MAX_DICT_SIZE and num_words, this is usually fine.
                // max count can be num_words, which is int.
                unique_words[j].count++;
                found = 1;
                break;
            }
        }

        if (found == 0) {
            // Word not found, add it to unique_words if capacity allows.
            if (num_unique_found < unique_words_capacity) {
                // Copy the word character by character.
                int k = 0;
                /*@
                  loop invariant 0 <= k <= MAX_WORD_LEN + 1;
                  loop invariant \forall integer l; 0 <= l < k ==> unique_words[num_unique_found].word[l] == current_word[l];
                  loop assigns k, unique_words[num_unique_found].word[0..MAX_WORD_LEN];
                  loop variant (MAX_WORD_LEN + 1) - k;
                */
                while (k <= MAX_WORD_LEN && current_word[k] != '\0') {
                    unique_words[num_unique_found].word[k] = current_word[k];
                    k++;
                }
                // Null-terminate the copied string.
                if (k <= MAX_WORD_LEN) {
                    unique_words[num_unique_found].word[k] = '\0';
                }

                unique_words[num_unique_found].count = 1;
                num_unique_found++;
            }
        }
    }

    return num_unique_found;
}

/*@
  requires \valid(source);
  requires \valid(destination);
  requires \strlen(source) <= MAX_WORD_LEN;
  requires \strlen(source) >= 0;
  assigns destination[0..MAX_WORD_LEN];
  ensures \forall integer i; 0 <= i <= \strlen(source) ==> destination[i] == source[i];
  ensures destination[\strlen(source)] == '\0';
  ensures \strlen(destination) == \strlen(source);
*/
// Helper function for string copy (not used in main logic to simplify, but for completeness)
void string_copy(char *destination, char *source) {
    int i = 0;
    /*@
      loop invariant 0 <= i <= MAX_WORD_LEN + 1;
      loop invariant \forall integer k; 0 <= k < i ==> destination[k] == source[k];
      loop assigns i, destination[0..MAX_WORD_LEN];
      loop variant (MAX_WORD_LEN + 1) - i;
    */
    while (i <= MAX_WORD_LEN && source[i] != '\0') {
        destination[i] = source[i];
        i++;
    }
    if (i <= MAX_WORD_LEN) {
        destination[i] = '\0';
    }
}

/*@
  requires \valid(s1);
  requires \valid(s2);
  requires \strlen(s1) <= MAX_WORD_LEN;
  requires \strlen(s2) <= MAX_WORD_LEN;
  assigns \nothing;
  ensures (\result == 1) <==> string_equal(s1, s2);
*/
// Helper function for string comparison (not used in main logic to simplify, but for completeness)
int string_compare(char *s1, char *s2) {
    int i = 0;
    /*@
      loop invariant 0 <= i <= MAX_WORD_LEN + 1;
      loop invariant \forall integer k; 0 <= k < i ==> s1[k] == s2[k];
      loop assigns i;
      loop variant (MAX_WORD_LEN + 1) - i;
    */
    while (i <= MAX_WORD_LEN && s1[i] != '\0' && s2[i] != '\0' && s1[i] == s2[i]) {
        i++;
    }
    return (s1[i] == '\0' && s2[i] == '\0') ? 1 : 0;
}
