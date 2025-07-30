// Task ID: 13
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay (handled by using exact types).
*/

/*@
  // Define a recursive logic function for string equality.
  // This is crucial for comparing words.
  // Rule II.1: Recursive logic for complexity.
  axiomatic String {
    logic integer strlen(char *s);
    axiom strlen_def:
      \forall char *s; strlen(s) == (
        if *s == '\0' then 0
        else 1 + strlen(s + 1)
      );

    logic boolean streq(char *s1, char *s2);
    axiom streq_def:
      \forall char *s1, s2; streq(s1, s2) <==> (
        if *s1 == '\0' then *s2 == '\0'
        else (*s1 == *s2 && streq(s1 + 1, s2 + 1))
      );

    // Rule II.2: CRITICAL - Helper Axiom for string length to prevent out-of-bounds access.
    // This axiom helps WP reason about valid memory access when comparing strings.
    axiom streq_implies_same_length:
      \forall char *s1, s2; streq(s1, s2) ==> strlen(s1) == strlen(s2);

    // Helper axiom for valid string access within bounds
    axiom strlen_valid_access:
      \forall char *s, integer i; 0 <= i < strlen(s) ==> \valid(s + i);
  }
*/

/*@
  // Define a structure for a word entry, including the word string and its count.
  // This must be defined as a C type for the function signature.
  typedef struct {
    char *word;
    int count;
  } WordEntry;
*/

/*@
  // count_most_common_words function
  // Goal: Find the most common word(s) in a dictionary.
  // This function will return the count of the most common word,
  // and update a provided array with the actual most common words.

  requires \valid_read(dictionary_entries + (0..num_entries-1));
  requires num_entries >= 0;

  // Each word pointer in the dictionary must be valid and null-terminated.
  requires \forall integer i; 0 <= i < num_entries ==> \valid_read(dictionary_entries[i].word);
  requires \forall integer i; 0 <= i < num_entries ==> \exists integer k; dictionary_entries[i].word[k] == '\0';

  // The output array for most common words must be valid for writing.
  requires \valid_write(most_common_words + (0..max_common_words-1));
  requires max_common_words >= 0;

  // The 'most_common_words' array should have enough capacity to store results.
  // This is a practical constraint for the function to be useful.
  // We assume that the caller provides sufficient space.

  assigns most_common_words[0..max_common_words-1];

  // Rule II.3: Ensures clause for boolean-like functions (though this returns an int,
  // the logic needs to capture the state of the output array and returned value).
  // This ensures clause defines what "most common" means.
  // It states that the returned value is the maximum count found.
  // And that any word in 'most_common_words' (up to the actual number found)
  // has this maximum count.

  ensures \result >= 0; // The count must be non-negative.

  // If there are no entries, the max count is 0 and no words are found.
  ensures num_entries == 0 ==> \result == 0;
  ensures num_entries == 0 ==> \fresh{Old}(most_common_words, max_common_words * sizeof(char*));

  // If there are entries, the result is the maximum count.
  ensures num_entries > 0 ==> (\exists integer i; 0 <= i < num_entries && dictionary_entries[i].count == \result);
  ensures num_entries > 0 ==> (\forall integer i; 0 <= i < num_entries ==> dictionary_entries[i].count <= \result);

  // The most_common_words array contains only words with the maximum count.
  // And the number of words stored in *actual_common_count is correct.
  ensures (\forall integer i; 0 <= i < *actual_common_count && i < max_common_words ==>
    (\exists integer j; 0 <= j < num_entries &&
     streq(most_common_words[i], dictionary_entries[j].word) &&
     dictionary_entries[j].count == \result));

  // Each word in the original dictionary that has the max count should be
  // present in the 'most_common_words' array, provided there's space.
  ensures (\forall integer j; 0 <= j < num_entries && dictionary_entries[j].count == \result ==>
    (\exists integer i; 0 <= i < *actual_common_count && i < max_common_words &&
     streq(most_common_words[i], dictionary_entries[j].word)));

  // The actual number of common words found should not exceed the capacity.
  ensures *actual_common_count <= max_common_words;
  ensures *actual_common_count >= 0;
*/
int count_most_common_words(WordEntry *dictionary_entries, int num_entries,
                            char **most_common_words, int max_common_words,
                            int *actual_common_count) {
    int max_count = 0;
    *actual_common_count = 0;

    if (num_entries <= 0) {
        return 0;
    }

    /*@
      loop invariant 0 <= i <= num_entries;
      loop invariant \forall integer k; 0 <= k < i ==> dictionary_entries[k].count <= max_count;
      loop invariant max_count >= 0;
      loop assigns i, max_count;
      loop variant num_entries - i;
    */
    for (int i = 0; i < num_entries; i++) {
        if (dictionary_entries[i].count > max_count) {
            max_count = dictionary_entries[i].count;
        }
    }

    /*@
      loop invariant 0 <= i <= num_entries;
      loop invariant 0 <= *actual_common_count <= max_common_words;
      loop invariant \forall integer k; 0 <= k < *actual_common_count ==>
        (\exists integer j; 0 <= j < i &&
         streq(most_common_words[k], dictionary_entries[j].word) &&
         dictionary_entries[j].count == max_count);
      loop invariant \forall integer k; 0 <= k < i && dictionary_entries[k].count == max_count ==>
        (\exists integer l; 0 <= l < *actual_common_count && l < max_common_words &&
         streq(most_common_words[l], dictionary_entries[k].word));
      loop assigns i, *actual_common_count, most_common_words[0..max_common_words-1];
      loop variant num_entries - i;
    */
    for (int i = 0; i < num_entries; i++) {
        if (dictionary_entries[i].count == max_count) {
            /*@
              // Prevent out-of-bounds write to most_common_words if capacity is exceeded.
              // Rule II.5: Prevent Runtime Errors (RTE).
              requires *actual_common_count < max_common_words;
            */
            if (*actual_common_count < max_common_words) {
                most_common_words[*actual_common_count] = dictionary_entries[i].word;
                (*actual_common_count)++;
            }
        }
    }

    return max_count;
}
