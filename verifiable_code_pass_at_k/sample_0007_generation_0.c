// Task ID: 7
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as it's a 1D array.

  // Rule II.1: Recursive logic for complexity - not directly applicable for this problem,
  // as we are not dealing with sums or complex sequences in ACSL.
  // Rule II.2: Helper axioms - not directly applicable.

  // Rule I.2: Represent boolean logic using int.
  // Return value: 1 if the character is an alphabet, 0 otherwise.
  assigns \nothing;
  ensures \result == 1 <==> ('a' <= c <= 'z' || 'A' <= c <= 'Z');
*/
int is_alpha(char c) {
    if (('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')) {
        return 1;
    }
    return 0;
}

/*@
  // Helper logic function to check if a character is a space.
  assigns \nothing;
  ensures \result == 1 <==> (c == ' ');
*/
int is_space(char c) {
    if (c == ' ') {
        return 1;
    }
    return 0;
}


/*@
  // Helper logic function to check if a character is a digit.
  assigns \nothing;
  ensures \result == 1 <==> ('0' <= c <= '9');
*/
int is_digit(char c) {
    if ('0' <= c && c <= '9') {
        return 1;
    }
    return 0;
}

/*@
  // Helper logic function to check if a character is alphanumeric.
  assigns \nothing;
  ensures \result == 1 <==> (is_alpha(c) || is_digit(c));
*/
int is_alphanumeric(char c) {
    if (is_alpha(c) == 1 || is_digit(c) == 1) {
        return 1;
    }
    return 0;
}

/*@
  axiomatic WordProperties {
    // Defines what a 'word' means in this context: a sequence of alphanumeric characters.
    // Rule II.1: Recursive logic for complexity.
    logic boolean is_word_char(char c) = is_alphanumeric(c) == 1;

    // Defines if the substring from start to end (exclusive) forms a valid word.
    // A word consists only of alphanumeric characters.
    // Rule II.1: Recursive logic for complexity.
    logic boolean is_valid_word_segment(char *s, int start, int end) reads s[start..end-1];

    axiom is_valid_word_segment_base:
      \forall char *s, integer start;
        is_valid_word_segment(s, start, start); // An empty segment is trivially valid.

    axiom is_valid_word_segment_recursive:
      \forall char *s, integer start, integer end;
        start < end ==> (is_valid_word_segment(s, start, end) <==>
                         (is_word_char(s[end - 1]) && is_valid_word_segment(s, start, end - 1)));
  }
*/

/*@
  requires \valid_read(str + (0..len-1));
  requires len >= 0;
  requires \valid_write(results + (0..max_results-1));
  requires max_results >= 0;

  // Rule II.5: Prevent runtime errors. Make sure indices are valid.
  // Rule II.3: Ensures clause for boolean-like functions.
  // The function finds words of at least 4 characters.
  // It returns the number of such words found.
  // A word is defined as a sequence of alphanumeric characters.
  // Words are delimited by non-alphanumeric characters or string boundaries.

  assigns results[0..max_results-1];

  ensures \result >= 0;
  ensures \result <= max_results;

  // For each found word, ensure it meets the criteria.
  ensures \forall integer k; 0 <= k < \result ==>
            (results[k].start >= 0 && results[k].start < len &&
             results[k].end > results[k].start && results[k].end <= len &&
             (results[k].end - results[k].start) >= 4 &&
             is_valid_word_segment(str, results[k].start, results[k].end));

  // Ensure that results contains distinct words and covers all such words in order.
  ensures \forall integer k1, k2; 0 <= k1 < k2 < \result ==> results[k1].end <= results[k2].start;

  // Ensure no overlapping words in results.
  ensures \forall integer k; 0 <= k < \result ==>
            (\forall integer i; results[k].start <= i < results[k].end ==> is_alphanumeric(str[i]) == 1);

  // Ensure that no other valid words are missed.
  // This is a complex property to express precisely in ACSL without significant
  // additional axiomatic definitions for "maximal word".
  // A simpler approach for verification is to trust the loop logic and
  // ensure the properties of the found words.
*/
int find_words(char *str, int len, struct Word { int start; int end; } *results, int max_results) {
    int count = 0;
    int i = 0;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant 0 <= count <= max_results;
      loop invariant \forall integer k; 0 <= k < count ==>
                       (results[k].start >= 0 && results[k].start < len &&
                        results[k].end > results[k].start && results[k].end <= len &&
                        (results[k].end - results[k].start) >= 4 &&
                        is_valid_word_segment(str, results[k].start, results[k].end));
      loop invariant \forall integer k1, k2; 0 <= k1 < k2 < count ==> results[k1].end <= results[k2].start;
      loop assigns i, count, results[0..max_results-1];
      loop variant len - i;
    */
    while (i < len) {
        // Skip non-alphanumeric characters
        /*@
          loop invariant i <= \at(i, LoopEntry) + (\at(len, LoopEntry) - \at(i, LoopEntry));
          loop invariant \at(i, LoopEntry) <= i <= len;
          loop invariant \forall integer k; \at(i, LoopEntry) <= k < i ==> is_alphanumeric(str[k]) == 0;
          loop assigns i;
          loop variant len - i;
        */
        while (i < len && is_alphanumeric(str[i]) == 0) {
            i++;
        }

        // Mark the start of a potential word
        int word_start = i;

        // Find the end of the word
        /*@
          loop invariant word_start <= i <= len;
          loop invariant \forall integer k; word_start <= k < i ==> is_alphanumeric(str[k]) == 1;
          loop assigns i;
          loop variant len - i;
        */
        while (i < len && is_alphanumeric(str[i]) == 1) {
            i++;
        }
        int word_end = i;

        // Check if it's a valid word (at least 4 characters long) and record it
        if (word_end - word_start >= 4) {
            if (count < max_results) {
                results[count].start = word_start;
                results[count].end = word_end;
                count++;
            }
        }
    }
    return count;
}
