// Task ID: 16
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: No \sum. Use recursive logic.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Use <==> for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic CharProperties {
    logic int is_lowercase(char c) reads c;
    axiom is_lowercase_def:
      \forall char c; is_lowercase(c) == (c >= 'a' && c <= 'z');

    logic int is_underscore(char c) reads c;
    axiom is_underscore_def:
      \forall char c; is_underscore(c) == (c == '_');
  }
*/

/*@
  // Helper logic to check if a substring is a sequence of lowercase letters.
  // This is a recursive logic function as per Rule II.1.
  axiomatic LowercaseSequence {
    logic int is_lowercase_sequence(char *s, int start, int end) reads s[start..end];

    axiom is_lowercase_sequence_base_empty:
      \forall char *s, int start, int end;
        start > end ==> is_lowercase_sequence(s, start, end) == 1;

    axiom is_lowercase_sequence_base_single:
      \forall char *s, int start;
        is_lowercase_sequence(s, start, start) == is_lowercase(s[start]);

    axiom is_lowercase_sequence_recursive:
      \forall char *s, int start, int end;
        start <= end ==>
        is_lowercase_sequence(s, start, end) ==
        (is_lowercase(s[start]) && is_lowercase_sequence(s, start + 1, end));

    // Helper axiom (Rule II.2) to make reasoning about non-lowercase characters easier.
    axiom is_lowercase_sequence_not_lowercase:
      \forall char *s, int start, int end, integer k;
        start <= k <= end && !is_lowercase(s[k]) ==> is_lowercase_sequence(s, start, end) == 0;
  }
*/

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function returns 1 if there exists a subsequence `s[i..j]` such that:
  // 1. `s[i..k]` is a lowercase sequence.
  // 2. `s[k+1]` is an underscore.
  // 3. `s[k+2..j]` is a lowercase sequence.
  // 4. `i <= k < k+1 < k+2 <= j` and all indices are within `0..len-1`.
  // This implies that the first lowercase sequence must have at least one char,
  // the underscore is one char, and the second lowercase sequence must have at least one char.
  ensures (\exists integer i, k, j;
            0 <= i && i <= k && k + 1 < len && k + 2 <= j && j < len &&
            is_lowercase_sequence(s, i, k) == 1 &&
            is_underscore(s[k+1]) == 1 &&
            is_lowercase_sequence(s, k + 2, j) == 1
          ) <==> (\result == 1);
*/
int find_sequence(char *s, int len) {
    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant \forall integer p; 0 <= p < i ==>
        !(\exists integer k, j;
            p <= k && k + 1 < len && k + 2 <= j && j < len &&
            is_lowercase_sequence(s, p, k) == 1 &&
            is_underscore(s[k+1]) == 1 &&
            is_lowercase_sequence(s, k + 2, j) == 1
          );
      loop assigns i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Find the start of the first lowercase sequence
        if (is_lowercase(s[i])) {
            int k = i; // k will be the end of the first lowercase sequence
            /*@
              loop invariant i <= k && k <= len;
              loop invariant is_lowercase_sequence(s, i, k-1) == 1;
              loop invariant \forall integer p; i <= p < k ==> is_lowercase(s[p]) == 1;
              loop assigns k;
              loop variant len - k;
            */
            while (k < len && is_lowercase(s[k])) {
                k++;
            }
            // k is now the first character that is NOT lowercase, or k == len
            // The first sequence is s[i..k-1]
            if (k > i) { // Ensure the first lowercase sequence has at least one character
                // Check for underscore
                if (k < len && is_underscore(s[k])) {
                    // Check for the second lowercase sequence
                    int j = k + 1; // j will be the start of the second lowercase sequence
                    /*@
                      loop invariant k + 1 <= j && j <= len;
                      loop invariant is_lowercase_sequence(s, k+1, j-1) == 1;
                      loop invariant \forall integer p; k + 1 <= p < j ==> is_lowercase(s[p]) == 1;
                      loop assigns j;
                      loop variant len - j;
                    */
                    while (j < len && is_lowercase(s[j])) {
                        j++;
                    }
                    // j is now the first character that is NOT lowercase, or j == len
                    // The second sequence is s[k+1..j-1]
                    if (j > k + 1) { // Ensure the second lowercase sequence has at least one character
                        return 1; // Found a match
                    }
                }
            }
        }
    }
    return 0; // No match found
}
