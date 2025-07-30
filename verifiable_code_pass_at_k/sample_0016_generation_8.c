// Task ID: 16
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic IsAlpha {
  logic boolean is_alpha_char(char c) = 'a' <= c <= 'z';
}
*/

/*@ axiomatic IsAllAlpha {
  logic boolean is_all_alpha(char *s, integer start, integer end) reads s[start .. end];

  axiom is_all_alpha_base:
    \forall char *s, integer start;
      is_all_alpha(s, start, start - 1) == \true;

  axiom is_all_alpha_recursive:
    \forall char *s, integer start, integer end;
      start <= end ==>
      is_all_alpha(s, start, end) == (is_alpha_char(s[end]) && is_all_alpha(s, start, end - 1));
}
*/

/*@
  requires \valid_read_range(s, 0, len - 1);
  requires len >= 0;

  assigns \nothing;

  // Rule II.3: ensures clause using logical equivalence.
  ensures (\exists integer i, j;
            0 <= i && i <= j && j < len &&
            is_all_alpha(s, i, j) &&
            (\exists integer k;
              j + 1 <= k && k < len &&
              s[k] == '_' &&
              is_all_alpha(s, k + 1, len - 1)
            )
          ) <==> (\result == 1);
*/
int find_alpha_underscore_alpha(char *s, int len) {
  /*@
    loop invariant 0 <= i <= len;
    loop invariant \forall integer k; 0 <= k < i ==>
      !(\exists integer j;
          k <= j && j < len &&
          is_all_alpha(s, k, j) &&
          (\exists integer l;
            j + 1 <= l && l < len &&
            s[l] == '_' &&
            is_all_alpha(s, l + 1, len - 1)
          )
        );
    loop assigns i;
    loop variant len - i;
  */
  for (int i = 0; i < len; i++) {
    // Try to find the first sequence of lowercase letters
    int j = i;
    /*@
      loop invariant i <= j <= len;
      loop invariant \forall integer k; i <= k < j ==> 'a' <= s[k] <= 'z';
      loop assigns j;
      loop variant len - j;
    */
    while (j < len && (s[j] >= 'a' && s[j] <= 'z')) {
      j++;
    }

    // If we found at least one letter
    if (j > i) {
      // Check for an underscore immediately after the first sequence
      if (j < len && s[j] == '_') {
        // Try to find the second sequence of lowercase letters
        int k = j + 1;
        int l = k;
        /*@
          loop invariant k <= l <= len;
          loop invariant \forall integer m; k <= m < l ==> 'a' <= s[m] <= 'z';
          loop assigns l;
          loop variant len - l;
        */
        while (l < len && (s[l] >= 'a' && s[l] <= 'z')) {
          l++;
        }

        // If we found at least one letter in the second sequence
        if (l > k) {
          return 1; // Found a pattern: [alpha]+_[alpha]+
        }
      }
    }
  }

  return 0; // No pattern found
}
