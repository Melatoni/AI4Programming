// Task ID: 44
// Generation: 0

/*@
  // Axiomatic block for helper logic
  axiomatic StringMatching {
    /*@
      // Rule II.1: Recursive logic for checking if a string starts with a word
      // Rule I.3: Correct pointer type for array parameters
      logic integer starts_with_recursive(char* s, char* word, integer s_len, integer word_len, integer k) =
        // Rule III.2: No parentheses around if-then-else
        // Rule III.1: Use ACSL if-then-else, not C ternary
        if k >= word_len then 1 // Word fully matched
        else if k >= s_len then 0 // String is shorter than word or exhausted
        else if s[k] == word[k] then starts_with_recursive(s, word, s_len, word_len, k + 1)
        else 0; // Mismatch
    */

    /*@
      // Helper function to check if string s starts with word
      // Rule I.3: Correct pointer type for array parameters
      logic integer starts_with(char* s, char* word, integer s_len, integer word_len) =
        if word_len == 0 then 1 // Empty word always matches
        else if s_len < word_len then 0 // String too short
        else starts_with_recursive(s, word, s_len, word_len, 0);
    */
  }
*/

/*@
  requires s != \null;
  requires word != \null;
  requires s_len >= 0;
  requires word_len >= 0;

  // Rule II.5: Prevent runtime errors (e.g., out-of-bounds access)
  // Ensure string and word have valid characters up to their lengths
  requires \valid(s + (0..s_len - 1)); // Rule III.3: Correct range syntax
  requires \valid(word + (0..word_len - 1));

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like return
  ensures starts_with(s, word, s_len, word_len) <==> (esult == 1);
*/
int matches_beginning(char* s, char* word, int s_len, int word_len) {
    // Rule I.2: Use int for booleans

    if (word_len == 0) {
        return 1; // An empty word always matches
    }

    if (s_len < word_len) {
        return 0; // String is shorter than the word
    }

    /*@
      loop invariant 0 <= i <= word_len;
      loop invariant 0 <= i <= s_len;
      // Rule II.4: Loop invariant for correctness
      loop invariant \forall integer k; 0 <= k < i ==> s[k] == word[k];
      loop assigns i;
      // Rule II.4: Loop variant for termination
      loop variant word_len - i;
    */
    for (int i = 0; i < word_len; i++) {
        if (s[i] != word[i]) {
            return 0; // Mismatch found
        }
    }

    return 1; // All characters matched
}
