// Task ID: 7
// Generation: 5

/*@
  // Rule I.1: No standard libraries. Rule I.2: Use int for booleans.

  // Rule II.1: Define recursive logic for complex properties.
  // This axiomatic block defines a predicate `is_word_char` and a function `is_word_at`.
  // `is_word_char(c)` checks if a character `c` is an alphanumeric character or underscore.
  // `is_word_at(s, start, len)` checks if the substring of `s` starting at `start`
  // with length `len` consists entirely of word characters.
  axiomatic WordProperties {
    logic boolean is_word_char(char c) =
      ('a' <= c && c <= 'z') ||
      ('A' <= c && c <= 'Z') ||
      ('0' <= c && c <= '9') ||
      (c == '_');

    logic boolean is_word_at(char *s, int start, int len);

    // Rule II.1: Base case for recursive logic.
    axiom is_word_at_base:
      \forall char *s, int start;
        is_word_at(s, start, 0);

    // Rule II.1: Recursive step for recursive logic.
    axiom is_word_at_rec:
      \forall char *s, int start, int len;
        len > 0 ==> (is_word_at(s, start, len) <==>
                     (is_word_char(s[start + len - 1]) && is_word_at(s, start, len - 1)));

    // Rule II.2: Helper axiom to prove that if a substring is a word,
    // then any prefix of that substring is also a word.
    axiom is_word_at_prefix:
      \forall char *s, int start, int len, int k;
        0 <= k <= len && is_word_at(s, start, len) ==> is_word_at(s, start, k);
  }

  // Helper axiomatic block to define the length of a string.
  axiomatic StringLength {
    logic integer string_length(char *s);

    axiom string_length_def:
      \forall char *s;
        string_length(s) == (\exists integer i; s[i] == '\0' &&
                                                 (\forall integer j; 0 <= j < i ==> s[j] != '\0'));
  }

  // The main function `find_long_words` aims to find words of at least 4 characters.
  // It takes a string `text`, an array `starts` to store starting indices,
  // an array `lengths` to store lengths, and `max_words` for the capacity of these arrays.
  // It returns the number of words found.
  // Rule II.5: Preconditions for input validity and potential overflow prevention.
  requires \valid(text);
  requires \valid(starts + (0..max_words-1));
  requires \valid(lengths + (0..max_words-1));
  requires max_words >= 0;
  requires string_length(text) >= 0; // Ensure text is a valid C string.

  // The function does not modify the input string `text`.
  assigns starts[0..max_words-1], lengths[0..max_words-1];

  // Postconditions:
  // - The returned value `\result` is non-negative and less than or equal to `max_words`.
  // - For each found word (up to `\result`), its start index and length are valid.
  // - Each found word must satisfy the definition of a word (alphanumeric or underscore).
  // - Each found word must be at least 4 characters long.
  // - All entries in `starts` and `lengths` beyond `\result` are unchanged.
  // - The function should correctly identify all such words in the string.
  //   This is captured by the `\forall` loop invariant and the final `ensures` clause.
  ensures 0 <= \result <= max_words;
  ensures \forall integer i; 0 <= i < \result ==>
            0 <= starts[i] < string_length(text) &&
            starts[i] + lengths[i] <= string_length(text) &&
            lengths[i] >= 4 &&
            is_word_at(text, starts[i], lengths[i]);

  // This ensures clause states that any word of length >= 4 found in the string
  // *must* be among the words stored in `starts` and `lengths`.
  // This is crucial for verifying that *all* relevant words are captured.
  ensures \forall integer start, length;
            0 <= start < string_length(text) &&
            start + length <= string_length(text) &&
            length >= 4 &&
            is_word_at(text, start, length) &&
            // Check that the character before (if any) is not a word character,
            // unless it's the beginning of the string.
            (start == 0 || !is_word_char(text[start - 1])) &&
            // Check that the character after (if any) is not a word character,
            // unless it's the end of the string.
            (start + length == string_length(text) || !is_word_char(text[start + length]))
            ==>
            (\exists integer i; 0 <= i < \result &&
                                starts[i] == start &&
                                lengths[i] == length);
*/
int find_long_words(char *text, int starts[], int lengths[], int max_words) {
    int word_count = 0;
    int i = 0;
    int n = 0; // Will hold string_length(text) for efficiency and proof.

    /*@
      loop invariant 0 <= i <= string_length(text);
      loop invariant n == string_length(text); // n correctly holds string length.
      loop assigns n;
      loop variant string_length(text) - i;
    */
    for (i = 0; text[i] != '\0'; i++) {
        n++;
    }
    // Now n holds string_length(text).

    i = 0; // Reset i for the main loop.
    /*@
      loop invariant 0 <= i <= n;
      loop invariant 0 <= word_count <= max_words;
      loop invariant \forall integer k; 0 <= k < word_count ==>
                       0 <= starts[k] < n &&
                       starts[k] + lengths[k] <= n &&
                       lengths[k] >= 4 &&
                       is_word_at(text, starts[k], lengths[k]);

      // This complex invariant ensures that we haven't missed any qualifying words
      // up to the current position `i`.
      loop invariant \forall integer start, length;
                       0 <= start < i &&
                       start + length <= n &&
                       length >= 4 &&
                       is_word_at(text, start, length) &&
                       (start == 0 || !is_word_char(text[start - 1])) &&
                       (start + length == n || !is_word_char(text[start + length]))
                       ==>
                       (\exists integer k; 0 <= k < word_count &&
                                           starts[k] == start &&
                                           lengths[k] == length);

      loop assigns i, word_count, starts[0..max_words-1], lengths[0..max_words-1];
      loop variant n - i;
    */
    while (i < n) {
        // Find the start of a word
        /*@
          loop invariant i <= \at(i,LoopEntry) + (\at(n,LoopEntry) - \at(i,LoopEntry));
          loop invariant \forall integer k; \at(i,LoopEntry) <= k < i ==> !is_word_char(text[k]);
          loop assigns i;
          loop variant n - i;
        */
        while (i < n && !is_word_char(text[i])) {
            i++;
        }

        int word_start = i;

        // Find the end of the word
        /*@
          loop invariant word_start <= i <= n;
          loop invariant \forall integer k; word_start <= k < i ==> is_word_char(text[k]);
          loop assigns i;
          loop variant n - i;
        */
        while (i < n && is_word_char(text[i])) {
            i++;
        }

        int word_length = i - word_start;

        // Rule II.5: Check for potential array bounds violation before access.
        if (word_length >= 4 && word_count < max_words) {
            starts[word_count] = word_start;
            lengths[word_count] = word_length;
            word_count++;
        }
    }

    return word_count;
}
