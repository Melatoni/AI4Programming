// Task ID: 16
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory Loop Annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.

  // Axiomatic block for character properties
  axiomatic CharProperties {
    logic boolean is_lowercase(char c) = (c >= 'a' && c <= 'z');
  }

  // Axiomatic block for sequence properties
  axiomatic SequenceProperties {
    // Recursive logic to check if a substring is a lowercase sequence
    logic boolean is_lowercase_seq(char *s, int start, int end) =
      if start > end then
        \true
      else if start == end then
        is_lowercase(s[start])
      else
        is_lowercase(s[start]) && is_lowercase_seq(s, start + 1, end);

    // Helper axiom: if a sequence is lowercase, its elements are lowercase
    axiom is_lowercase_seq_implies_element_lowercase:
      \forall char *s, integer start, integer end;
        is_lowercase_seq(s, start, end) ==>
          \forall integer i; start <= i <= end ==> is_lowercase(s[i]);
  }
*/

/*@
  requires \valid_read(s + (0..len - 1));
  requires len >= 0;

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence.
  // The function returns 1 if there exists a valid sequence of lowercase letters
  // joined with an underscore, otherwise 0.
  ensures (\exists integer i, integer j, integer k;
             0 <= i < len && // Start of first lowercase sequence
             0 <= j < len && // End of first lowercase sequence
             i <= j &&
             is_lowercase_seq(s, i, j) &&
             j + 1 < len && s[j+1] == '_' && // Underscore in between
             j + 2 < len && // Start of second lowercase sequence
             0 <= k < len && // End of second lowercase sequence
             j + 2 <= k &&
             is_lowercase_seq(s, j + 2, k)
          ) <==> (\result == 1);
*/
int find_sequence(char *s, int len) {
    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer prev_i, prev_j, prev_k;
        0 <= prev_i < i && prev_i <= prev_j && prev_j + 1 < i && prev_j + 2 < i && prev_j + 2 <= prev_k < i ==>
        !(is_lowercase_seq(s, prev_i, prev_j) && s[prev_j+1] == '_' && is_lowercase_seq(s, prev_j+2, prev_k));
      loop assigns i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Find the end of the first lowercase sequence
        int j = i;
        /*@
          loop invariant i <= j <= len;
          loop invariant \forall integer k; i <= k < j ==> is_lowercase(s[k]);
          loop assigns j;
          loop variant len - j;
        */
        while (j < len && is_lowercase(s[j])) {
            j++;
        }
        // After this loop, j is the index of the first non-lowercase char or len.
        // The first sequence is s[i..j-1]

        // Check if a valid first lowercase sequence was found
        if (j > i) { // i.e., at least one lowercase character was found
            // Check for underscore
            if (j < len && s[j] == '_') {
                // Find the end of the second lowercase sequence
                int k = j + 1;
                /*@
                  loop invariant j + 1 <= k <= len;
                  loop invariant \forall integer l; j + 1 <= l < k ==> is_lowercase(s[l]);
                  loop assigns k;
                  loop variant len - k;
                */
                while (k < len && is_lowercase(s[k])) {
                    k++;
                }
                // After this loop, k is the index of the first non-lowercase char or len.
                // The second sequence is s[j+1..k-1]

                // Check if a valid second lowercase sequence was found
                if (k > j + 1) { // i.e., at least one lowercase character was found after '_'
                    return 1;
                }
            }
        }
    }
    return 0;
}
