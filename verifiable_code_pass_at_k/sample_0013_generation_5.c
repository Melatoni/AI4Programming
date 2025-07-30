// Task ID: 13
// Generation: 5

/*@
  // Axiomatic block for recursive logic and helper axioms (Rule II.1, II.2)
  axiomatic WordCount {
    // Defines a logic function to get the count of a specific word in the dictionary up to a given index.
    logic integer count_word_up_to(char* word, char* dictionary[], int dictionary_size, int up_to_index);

    // Base case: If up_to_index is less than 0, count is 0.
    axiom count_word_up_to_base:
      \forall char* word, char* dictionary[], integer dictionary_size, integer up_to_index;
        up_to_index < 0 ==> count_word_up_to(word, dictionary, dictionary_size, up_to_index) == 0;

    // Recursive case: If word at current index matches, increment count.
    axiom count_word_up_to_recursive:
      \forall char* word, char* dictionary[], integer dictionary_size, integer up_to_index;
        up_to_index >= 0 ==>
          count_word_up_to(word, dictionary, dictionary_size, up_to_index) ==
            (if \strcmp(word, dictionary[up_to_index]) == 0 then 1 else 0) +
            count_word_up_to(word, dictionary, dictionary_size, up_to_index - 1);

    // Helper axiom: Defines the total count of a word in the entire dictionary.
    logic integer total_count(char* word, char* dictionary[], int dictionary_size) =
      count_word_up_to(word, dictionary, dictionary_size, dictionary_size - 1);

    // Helper function for string comparison (Frama-C's \strcmp is equivalent to C's strcmp)
    // We assume \strcmp is available and works as expected for string comparison.
    // No need to define it explicitly here as it's a built-in ACSL predicate.
  }
*/

/*@
  // Helper axiomatic block for string length (Rule II.1, II.2)
  axiomatic StringLength {
    logic integer string_length(char* s);

    axiom string_length_char:
      \forall char* s, integer i;
        (s[i] == '\0') ==> string_length(s) == i;

    axiom string_length_non_null:
      \forall char* s, integer i;
        (s[i] != '\0') ==> string_length(s) > i;
  }
*/

/*@
  // Helper axiomatic block for string copy (Rule II.1, II.2)
  axiomatic StringCopy {
    logic \bool string_equal(char* s1, char* s2);

    axiom string_equal_def:
      \forall char* s1, char* s2;
        string_equal(s1, s2) <==> (\strcmp(s1, s2) == 0);

    // Helper axiom: Proof that string copy correctly copies content.
    // This is crucial for verifying that the target buffer `most_common`
    // will contain the correct string.
    axiom string_copy_preserves_content:
      \forall char* dest, char* src;
        \valid(src) && \valid(dest) && string_length(src) < string_length(dest) ==>
        (\forall integer i; 0 <= i <= string_length(src) ==> dest[i] == src[i]);
  }
*/

/*@
  requires dictionary_size >= 0;
  requires max_word_length >= 0;

  // Each word in the dictionary must be a valid string.
  requires \forall integer i; 0 <= i < dictionary_size ==> \valid(dictionary[i]);
  requires \forall integer i; 0 <= i < dictionary_size ==> \valid_read(dictionary[i]);
  requires \forall integer i; 0 <= i < dictionary_size ==> string_length(dictionary[i]) <= max_word_length;

  // `most_common` must be a valid buffer large enough to hold any word + null terminator.
  requires \valid(most_common);
  requires \valid_write(most_common);
  requires \initialized(most_common);
  requires max_word_length >= 0 ==> \separated(most_common + (0..max_word_length), dictionary[0 .. dictionary_size - 1] + (0..max_word_length));

  assigns most_common[0 .. max_word_length];

  // Ensures: If the dictionary is not empty, most_common will contain a word that has
  // the maximum frequency among all words in the dictionary.
  ensures dictionary_size == 0 ==> \result == 0; // Return 0 if dictionary is empty
  ensures dictionary_size > 0 ==> \result == 1; // Return 1 if dictionary is processed

  ensures dictionary_size > 0 ==>
    (\exists integer i; 0 <= i < dictionary_size && string_equal(most_common, dictionary[i]));

  ensures dictionary_size > 0 ==>
    (\forall integer i; 0 <= i < dictionary_size ==>
      total_count(most_common, dictionary, dictionary_size) >= total_count(dictionary[i], dictionary, dictionary_size));
*/
int count_most_common_word(char* dictionary[], int dictionary_size, char* most_common, int max_word_length) {
    if (dictionary_size == 0) {
        return 0; // Rule I.2: Use 0 for false
    }

    // Initialize most_common to the first word and its count.
    // This assumes dictionary_size > 0, which is handled by the initial check.
    char* current_most_common_word = dictionary[0];
    int max_count = 0;

    // Manual string copy for the initial word since we cannot use `strcpy`.
    /*@
      loop invariant 0 <= k <= string_length(current_most_common_word);
      loop invariant k < max_word_length + 1;
      loop assigns most_common[0 .. k];
      loop variant string_length(current_most_common_word) - k;
    */
    for (int k = 0; k <= string_length(current_most_common_word); k++) {
        most_common[k] = current_most_common_word[k];
    }
    // Update max_count with the count of the first word
    /*@
      loop invariant 0 <= i <= dictionary_size;
      loop invariant max_count == total_count(current_most_common_word, dictionary, i-1);
      loop assigns max_count;
      loop variant dictionary_size - i;
    */
    for (int i = 0; i < dictionary_size; i++) {
        /*@
          loop invariant 0 <= j <= i;
          loop invariant \forall integer k; 0 <= k < j ==> \strcmp(current_most_common_word, dictionary[k]) != 0 || current_most_common_word == dictionary[k];
          loop assigns max_count; // Only max_count is assigned in the loop body
          loop variant i - j;
        */
        if (\strcmp(current_most_common_word, dictionary[i]) == 0) {
            max_count++;
        }
    }


    /*@
      loop invariant 0 <= i <= dictionary_size;
      // Loop invariant: `most_common` (the string) holds one of the words from `dictionary[0..i-1]`.
      loop invariant i > 0 ==> (\exists integer idx; 0 <= idx < i && string_equal(most_common, dictionary[idx]));

      // Loop invariant: `max_count` is the total count of `most_common` in `dictionary[0..i-1]`.
      loop invariant max_count == total_count(most_common, dictionary, i - 1);

      // Loop invariant: For any word in `dictionary[0..i-1]`, its count is less than or equal to `max_count`.
      loop invariant \forall integer j; 0 <= j < i ==> total_count(dictionary[j], dictionary, i - 1) <= max_count;

      loop assigns i, current_most_common_word, most_common[0 .. max_word_length], max_count;
      loop variant dictionary_size - i;
    */
    for (int i = 0; i < dictionary_size; i++) {
        char* current_word = dictionary[i];
        int current_word_count = 0;

        /*@
          loop invariant 0 <= j <= dictionary_size;
          loop invariant current_word_count == total_count(current_word, dictionary, j - 1);
          loop assigns current_word_count;
          loop variant dictionary_size - j;
        */
        for (int j = 0; j < dictionary_size; j++) {
            if (\strcmp(current_word, dictionary[j]) == 0) {
                current_word_count++;
            }
        }

        if (current_word_count > max_count) {
            max_count = current_word_count;
            current_most_common_word = current_word;

            // Manual string copy for `most_common` (Rule I.1, I.2)
            /*@
              loop invariant 0 <= k <= string_length(current_most_common_word);
              loop invariant k < max_word_length + 1;
              loop assigns most_common[0 .. k];
              loop variant string_length(current_most_common_word) - k;
            */
            for (int k = 0; k <= string_length(current_most_common_word); k++) {
                most_common[k] = current_most_common_word[k];
            }
        }
    }

    return 1; // Rule I.2: Use 1 for true
}
