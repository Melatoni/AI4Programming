// Task ID: 16
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: Ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  // Axiomatic block to define properties of lowercase letters.
  axiomatic LowercaseLetters {
    // A predicate to check if a character is a lowercase letter.
    logic boolean is_lowercase_letter(char c) = (c >= 'a' && c <= 'z');
  }
*/

/*@
  // Axiomatic block to define properties of sequences of lowercase letters.
  axiomatic SequenceProperties {
    // Recursive logic function to check if a substring contains only lowercase letters.
    // Rule II.1: Recursive logic for complexity.
    logic boolean all_lowercase(char* s, int start, int end) =
      (start > end) ||
      (is_lowercase_letter(s[start]) && all_lowercase(s, start + 1, end));

    // Helper axiom: If all characters are lowercase, and the string is not empty,
    // then the first character must be lowercase.
    // Rule II.2: CRITICAL - Helper Axioms.
    axiom all_lowercase_implies_first_is_lowercase:
      \forall char* s, integer start, integer end;
        start <= end && all_lowercase(s, start, end) ==> is_lowercase_letter(s[start]);

    // Helper axiom: If all characters are lowercase, and the string is not empty,
    // then the last character must be lowercase.
    axiom all_lowercase_implies_last_is_lowercase:
      \forall char* s, integer start, integer end;
        start <= end && all_lowercase(s, start, end) ==> is_lowercase_letter(s[end]);

    // Helper axiom: If a sequence of characters satisfies all_lowercase,
    // then any sub-sequence also satisfies it.
    axiom all_lowercase_subsequence:
      \forall char* s, integer start, integer end, integer sub_start, integer sub_end;
        start <= sub_start <= sub_end <= end && all_lowercase(s, start, end) ==> all_lowercase(s, sub_start, sub_end);
  }
*/

/*@
  requires \valid_read_string(s);
  requires len >= 0;
  requires \for_all integer k; 0 <= k < len ==> \valid_read(s + k);

  // Rule II.5: Prevent Runtime Errors (RTE) - ensure len is not excessively large
  // to prevent potential overflow in computations involving indices, although
  // for this specific problem, it's less critical unless len is near INT_MAX.
  // For string processing, usually the length is bounded by memory.
  // This is more of a generic placeholder for "consider bounds".

  assigns \nothing;

  // Rule II.3: CRITICAL - `ensures` Clause for Boolean-like Functions.
  // The function returns 1 if there exists a sequence of the form `word_word`
  // where word is a sequence of one or more lowercase letters.
  ensures (\exists integer i, integer j, integer k;
             0 <= i && i < j && j < k && k < len &&
             all_lowercase(s, i, j - 1) && // First word
             s[j] == '_' &&               // Underscore separator
             all_lowercase(s, j + 1, k)   // Second word
          ) <==> (esult == 1);
*/
int has_word_underscore_word(char* s, int len) {
    /*@
      loop invariant 0 <= i <= len;
      // We are looking for a pattern like word_word.
      // i is the potential start of the first word.
      // The invariant states that no such pattern has been found starting before i.
      loop invariant \for_all integer p, integer q, integer r;
        0 <= p && p < q && q < r && r < i &&
        all_lowercase(s, p, q - 1) && s[q] == '_' && all_lowercase(s, q + 1, r) ==> \false;
      loop assigns i, j, k; // i, j, k are loop variables, not necessarily assigned in outer loop.
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        /*@
          loop invariant i <= j <= len;
          // j is the potential end of the first word + 1 (i.e., start of '_').
          // The invariant states that for the current i, no valid first word has been found
          // ending before j (i.e., s[i..j-1] is not a valid first word for a match).
          loop invariant \for_all integer p;
            i <= p < j && all_lowercase(s, i, p) ==> \false; // No first word ending at p.
          loop assigns j, k;
          loop variant len - j;
        */
        for (int j = i; j < len; j++) {
            // Check if s[i..j] is a word (all lowercase and at least one char)
            // and if s[j+1] is an underscore.
            if (j + 1 < len && s[j + 1] == '_' && all_lowercase(s, i, j)) {
                // We found a potential first word (s[i..j]) and an underscore at s[j+1].
                // Now look for the second word starting at j+2.
                /*@
                  loop invariant j + 2 <= k <= len;
                  // k is the potential end of the second word + 1.
                  // The invariant states that for the current i, j, no valid second word has been found
                  // ending before k (i.e., s[j+2..k-1] is not a valid second word for a match).
                  loop invariant \for_all integer p;
                    j + 1 < p < k && all_lowercase(s, j + 2, p) ==> \false; // No second word ending at p.
                  loop assigns k;
                  loop variant len - k;
                */
                for (int k = j + 2; k < len; k++) {
                    // Check if s[j+2..k] is a word.
                    if (all_lowercase(s, j + 2, k)) {
                        return 1; // Found a sequence: s[i..j]_s[j+2..k]
                    }
                }
            }
        }
    }
    return 0; // No such sequence found.
}
