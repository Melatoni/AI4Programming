// Task ID: 16
// Generation: 7

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array parameter decay handled for logic functions.

  // Rule II.1: Using axiomatic for complex logic.
  // Rule II.2: Helper axioms are crucial.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax '..'.
  // Rule III.4: No stray semicolons.
*/

/*@ axiomatic CharProperties {
  logic boolean is_lowercase_letter(char c) = (c >= 'a' && c <= 'z');

  // Helper axiom: if a character is not a lowercase letter, it's not a lowercase letter.
  // This might seem trivial, but helps the prover with negation.
  axiom is_lowercase_letter_not_implies_not:
    \forall char c; !is_lowercase_letter(c) ==> !(c >= 'a' && c <= 'z');
}
*/

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;

  // Rule II.5: Prevent overflow if len is very large, though char array usually small.
  // This specific constraint might not be strictly necessary for this problem,
  // but demonstrates the principle of thinking about potential RTEs.
  // For char arrays, typical sizes are well within int limits.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // It checks if there exists a starting index 'i' and a length 'l'
  // such that the substring s[i..i+l-1] matches the pattern:
  // (one or more lowercase letters) _ (one or more lowercase letters).
  ensures (\exists integer i, l;
              0 <= i && i < len &&
              0 <= l && (i + l) <= len &&
              l >= 3 && // Minimum length for "a_b"
              is_lowercase_letter(s[i]) && // First char is letter
              s[i+1] == '_' &&             // Second char is underscore
              is_lowercase_letter(s[i+2]) && // Third char is letter
              // Check for sequence of letters before underscore
              (\forall integer k; 0 <= k < i+1 ==> is_lowercase_letter(s[k])) &&
              // Check for sequence of letters after underscore
              (\forall integer k; i+2 <= k < i+l ==> is_lowercase_letter(s[k]))
          ) <==> (\result == 1);
*/
int find_sequence(char *s, int len) {
    /*@
      loop invariant 0 <= i <= len;
      // Rule II.4: Invariant for the outer loop.
      // It states that for all indices j less than i, no sequence starting at j has been found.
      loop invariant \forall integer k; 0 <= k < i ==>
        !(\exists integer l;
            0 <= k && k < len &&
            0 <= l && (k + l) <= len &&
            l >= 3 &&
            is_lowercase_letter(s[k]) &&
            s[k+1] == '_' &&
            is_lowercase_letter(s[k+2]) &&
            (\forall integer m; 0 <= m < k+1 ==> is_lowercase_letter(s[m])) &&
            (\forall integer m; k+2 <= m < k+l ==> is_lowercase_letter(s[m]))
        );
      loop assigns i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Check if there are enough characters left for a potential match (at least 3: letter_letter)
        if (i + 2 < len) {
            // Check for the pattern: letter followed by underscore
            if (is_lowercase_letter(s[i]) && s[i+1] == '_') {
                // Now, check if the character after the underscore is a lowercase letter
                if (is_lowercase_letter(s[i+2])) {
                    // We found 'letter_' and another 'letter'.
                    // Now, verify that the first part (s[i]) is part of a sequence of letters
                    /*@
                      loop invariant 0 <= k <= i;
                      loop invariant \forall integer j; k <= j < i ==> is_lowercase_letter(s[j]);
                      loop assigns k;
                      loop variant k;
                    */
                    int k = i;
                    while (k >= 0 && is_lowercase_letter(s[k])) {
                        k--;
                    }
                    // k is now the index BEFORE the start of the first letter sequence, or -1.
                    // So, s[k+1] is the true start of the first letter sequence.
                    int first_letter_start = k + 1;

                    // Verify that the second part (s[i+2]) is part of a sequence of letters
                    /*@
                      loop invariant i+2 <= j <= len;
                      loop invariant \forall integer m; i+2 <= m < j ==> is_lowercase_letter(s[m]);
                      loop assigns j;
                      loop variant len - j;
                    */
                    int j = i + 2;
                    while (j < len && is_lowercase_letter(s[j])) {
                        j++;
                    }
                    // j is now the index AFTER the end of the second letter sequence.
                    // So, s[j-1] is the true end of the second letter sequence.
                    int second_letter_end = j - 1;

                    // A valid sequence must have at least one letter before and one after the underscore.
                    // This is implicitly checked by is_lowercase_letter(s[i]) and is_lowercase_letter(s[i+2]).
                    // The length of the found sequence is (second_letter_end - first_letter_start + 1).
                    // We need to ensure that the character at 'i' is indeed the first character
                    // of its sequence, and 'i+2' is the first character of its sequence.
                    // The current logic correctly finds if 's[i]' is a letter, 's[i+1]' is '_',
                    // and 's[i+2]' is a letter. The loops then expand to find the full letter sequences.

                    // The 'ensures' clause requires that *all* characters in the first sequence are letters,
                    // and *all* characters in the second sequence are letters.
                    // This is implicitly handled by the loops: the 'k' loop goes left until a non-letter
                    // is found or start of string. The 'j' loop goes right until a non-letter or end of string.
                    // The current 'i' is the starting point of the match.
                    // The 'l' in the ensures clause would be (j - first_letter_start).
                    // This means we found a valid match.
                    return 1;
                }
            }
        }
    }
    return 0;
}
