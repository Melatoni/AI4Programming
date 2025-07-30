// Task ID: 7
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as we are dealing with char pointers.
*/

/*@ axiomatic WordProperties {
  // Rule II.1: Recursive logic for complexity.
  // Defines if a character is considered a word character (alphabetic).
  logic boolean is_word_char(char c) = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');

  // Defines the length of a word starting at index `start` in string `s`.
  // A word is a sequence of word characters.
  logic integer word_length(char* s, integer start, integer len) =
    if start >= len || !is_word_char(s[start]) then 0
    else 1 + word_length(s, start + 1, len);

  // Defines if a word of at least 4 characters exists starting at or after `start`
  // and ending before `len`.
  logic boolean has_long_word_from(char* s, integer start, integer len) =
    if start >= len then \false
    else (word_length(s, start, len) >= 4) || has_long_word_from(s, start + 1, len);

  // Rule II.2: CRITICAL - Helper Axioms.
  // Axiom to prove that if a character is not a word char, word_length is 0.
  axiom word_length_non_word_char:
    \forall char* s, integer start, integer len;
      (start < len && !is_word_char(s[start])) ==> word_length(s, start, len) == 0;

  // Axiom to prove that if a word starts, its length is at least 1.
  axiom word_length_word_char:
    \forall char* s, integer start, integer len;
      (start < len && is_word_char(s[start])) ==> word_length(s, start, len) >= 1;

  // Axiom to relate has_long_word_from to word_length at current position.
  axiom has_long_word_from_current_or_next:
    \forall char* s, integer start, integer len;
      start < len ==>
        (has_long_word_from(s, start, len) <==>
         (word_length(s, start, len) >= 4 || has_long_word_from(s, start + 1, len)));
}
*/

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;
  // Rule II.5: Prevent runtime errors. Ensure string is null-terminated if len is its actual length.
  // For this problem, we assume `len` is the precise length of the string segment to check.
  // If `s` is a C-string, `s[len]` must be `\0`.
  requires \valid_read(s + len); // ensures s[len] can be read, important for string functions.
  requires s[len] == '\0'; // Ensures null termination for safe string processing.

  assigns \nothing;

  // Rule II.3: CRITICAL - ensures clause for boolean-like functions uses logical equivalence.
  ensures (\exists integer i; 0 <= i < len && word_length(s, i, len) >= 4) <==> (\result == 1);
*/
int has_long_word_regex(char* s, int len) {
    int i = 0;
    /*@
      loop invariant 0 <= i <= len;
      // Rule II.4: Mandatory loop invariant.
      // No long word found in the prefix s[0..i-1]
      loop invariant \forall integer k; 0 <= k < i ==> word_length(s, k, len) < 4;
      loop assigns i;
      // Rule II.4: Mandatory loop variant.
      loop variant len - i;
    */
    while (i < len) {
        // Find the start of a potential word
        /*@
          loop invariant i <= \at(i,LoopEntry) + (\at(len,LoopEntry) - \at(i,LoopEntry)); // i doesn't exceed len.
          loop invariant \forall integer k; \at(i,LoopEntry) <= k < i ==> !is_word_char(s[k]);
          loop assigns i;
          loop variant len - i;
        */
        while (i < len && !is_word_char(s[i])) { // Rule II.1: uses axiomatic logic function
            i++;
        }

        // If we reached the end of the string, no more words.
        if (i >= len) {
            break;
        }

        // Now i is at the start of a word. Find its end.
        int word_start = i;
        /*@
          loop invariant word_start <= i <= len;
          loop invariant \forall integer k; word_start <= k < i ==> is_word_char(s[k]);
          loop assigns i;
          loop variant len - i;
        */
        while (i < len && is_word_char(s[i])) { // Rule II.1: uses axiomatic logic function
            i++;
        }

        // Calculate the length of the found word
        int current_word_length = i - word_start;

        // Check if the word is at least 4 characters long
        if (current_word_length >= 4) {
            return 1; // Rule I.2: Returns 1 for true.
        }
    }

    return 0; // Rule I.2: Returns 0 for false.
}
