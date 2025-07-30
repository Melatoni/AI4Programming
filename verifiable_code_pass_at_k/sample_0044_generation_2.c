// Task ID: 44
// Generation: 2

/*@
  axiomatic String {
    // Rule II.1: Recursive logic for string length.
    logic integer strlen_logic(char *s);

    axiom strlen_null{
      requires \valid(s);
      ensures strlen_logic(s) == 0 <==> s[0] == '\0';
    }

    axiom strlen_rec{
      requires \valid(s) && s[0] != '\0';
      ensures strlen_logic(s) == 1 + strlen_logic(s + 1);
    }

    // Rule II.2: Helper axiom for strlen_logic.
    // Proves that strlen_logic is non-negative.
    axiom strlen_non_negative{
      requires \valid(s);
      ensures strlen_logic(s) >= 0;
    }

    // Rule II.1: Recursive logic for string equality up to a given length.
    logic boolean streq_n_logic(char *s1, char *s2, integer n);

    axiom streq_n_base{
      requires n <= 0;
      ensures streq_n_logic(s1, s2, n) == \true;
    }

    axiom streq_n_rec{
      requires n > 0;
      requires \valid(s1) && \valid(s2);
      ensures streq_n_logic(s1, s2, n) == (s1[0] == s2[0] && streq_n_logic(s1 + 1, s2 + 1, n - 1));
    }

    // Rule II.2: Helper axiom for streq_n_logic.
    // If strings are equal for n, they are also equal for any k < n.
    axiom streq_n_sub_length{
      requires \valid(s1) && \valid(s2);
      requires streq_n_logic(s1, s2, n);
      requires 0 <= k <= n;
      ensures streq_n_logic(s1, s2, k);
    }
  }
*/

/*@
  requires \valid(str);
  requires \valid(word);
  requires \separated(str, word);

  // Rule II.5: Prevent potential out-of-bounds access if word is longer than str.
  // This is implicitly handled by strlen_logic, but good to make it explicit if possible.
  // Not strictly necessary here as the logic handles it, but kept for demonstration.
  requires strlen_logic(word) <= strlen_logic(str);

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (streq_n_logic(str, word, strlen_logic(word))) <==> (result == 1);
*/
int match_beginning(char *str, char *word) { // Rule I.2: Uses int, not bool.
    /*@
      // Rule II.5: Prevent potential overflow if lengths are extremely large.
      // Not strictly an overflow for int, but for the logic of strlen_logic.
      // Since strlen_logic results in integer, it's covered by integer range.
      requires strlen_logic(word) >= 0;
    */
    int word_len = 0;
    /*@
      loop invariant 0 <= word_len <= strlen_logic(word);
      loop invariant \forall integer k; 0 <= k < word_len ==> word[k] != '\0';
      loop assigns word_len;
      loop variant strlen_logic(word) - word_len;
    */
    while (word[word_len] != '\0') {
        word_len++;
    }

    /*@
      loop invariant 0 <= i <= word_len;
      // Rule II.4: Invariant capturing the progress and the partial match.
      loop invariant \forall integer k; 0 <= k < i ==> str[k] == word[k];
      loop assigns i;
      loop variant word_len - i;
    */
    for (int i = 0; i < word_len; i++) {
        // Rule II.5: Prevent potential out-of-bounds access.
        // Already implicitly handled by loop invariant (i < word_len and word_len <= strlen_logic(word)).
        // Also \valid(str) and \valid(word) ensure initial validity.
        // The loop condition i < word_len and the previous check word_len <= strlen_logic(str)
        // ensure str[i] and word[i] are valid accesses.
        if (str[i] != word[i]) {
            return 0; // Corresponds to the 'false' case of the ensures clause.
        }
    }

    return 1; // Corresponds to the 'true' case of the ensures clause.
}
