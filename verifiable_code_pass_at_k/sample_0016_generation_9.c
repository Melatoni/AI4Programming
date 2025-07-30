// Task ID: 16
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Define an axiomatic block for character properties.
  axiomatic CharProperties {
    logic boolean is_lowercase(char c) = (c >= 'a' && c <= 'z');
  }

  // Rule II.1: Recursive logic for complexity.
  // Define an axiomatic block for sequence properties.
  axiomatic SequenceProperties {
    // Check if a substring contains only lowercase letters.
    logic boolean is_lowercase_sequence(char *s, integer start, integer end) reads s[start..end];
    
    axiom is_lowercase_sequence_base:
      \forall char *s, integer start;
        is_lowercase_sequence(s, start, start) <==> is_lowercase(s[start]);

    axiom is_lowercase_sequence_recursive:
      \forall char *s, integer start, integer end;
        start < end ==> (is_lowercase_sequence(s, start, end) <==> (is_lowercase(s[end]) && is_lowercase_sequence(s, start, end - 1)));

    // Rule II.2: Helper axioms for recursive functions.
    // A helper axiom to ensure that if a sequence is lowercase, all its elements are.
    axiom is_lowercase_sequence_element:
      \forall char *s, integer start, integer end, integer k;
        start <= k <= end && is_lowercase_sequence(s, start, end) ==> is_lowercase(s[k]);
  }

  // Rule II.5: Prevent Runtime Errors (RTE).
  // Ensure the string is not null and has a positive length.
  // Ensure the length does not exceed INT_MAX for array indexing.
  requires s != \null;
  requires len > 0;
  requires len <= 2147483647; // INT_MAX from limits.h for array indexing safety.

  assigns \nothing;

  // Rule II.3: ensures clause uses logical equivalence.
  // The function returns 1 if there exists a subsequence of the form lowercase_sequence_1 + '_' + lowercase_sequence_2.
  // The function returns 0 if no such subsequence exists.
  ensures (\exists integer i, j, k;
              0 <= i < j - 1 < k < len &&
              s[j-1] == '_' &&
              is_lowercase_sequence(s, i, j - 2) &&
              is_lowercase_sequence(s, j, k)
          ) <==> (\result == 1);
*/
int find_lowercase_underscore_sequence(char *s, int len) {
  /*@
    loop invariant 0 <= i <= len;
    loop invariant \forall integer x, y, z;
      0 <= x < y - 1 < z < i ==> !(s[y-1] == '_' && is_lowercase_sequence(s, x, y - 2) && is_lowercase_sequence(s, y, z));
    loop assigns i;
    loop variant len - i;
  */
  for (int i = 0; i < len; ++i) {
    if (s[i] == '_') {
      // Found an underscore. Now check if it's flanked by lowercase sequences.
      // Rule III.1: No C-style ternary in ACSL.
      // Rule III.2: No parentheses around if-then-else.
      // Rule III.3: Correct range syntax.

      /*@
        loop invariant 0 <= j <= i;
        loop invariant \forall integer x;
          0 <= x < j ==> !is_lowercase(s[x]);
        loop assigns j;
        loop variant j;
      */
      int start_seq1 = -1;
      for (int j = i - 1; j >= 0; --j) {
        if (!is_lowercase(s[j])) {
          break;
        }
        start_seq1 = j;
      }

      if (start_seq1 != -1) { // Found a potential first sequence.
        /*@
          loop invariant i + 1 <= k <= len;
          loop invariant \forall integer x;
            i + 1 <= x < k ==> !is_lowercase(s[x]);
          loop assigns k;
          loop variant len - k;
        */
        int end_seq2 = -1;
        for (int k = i + 1; k < len; ++k) {
          if (!is_lowercase(s[k])) {
            break;
          }
          end_seq2 = k;
        }

        if (end_seq2 != -1) { // Found a potential second sequence.
          // Check if sequences are non-empty
          if (start_seq1 <= i - 1 && i + 1 <= end_seq2) {
            return 1; // Found a match.
          }
        }
      }
    }
  }
  return 0; // No match found.
}
