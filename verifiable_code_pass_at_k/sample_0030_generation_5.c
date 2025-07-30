// Task ID: 30
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Recursive logic for complexity.
  // Helper axiomatic block to define properties of substrings.
  axiomatic SubstringProperties {
    logic integer string_length(char *s);
    axiom string_length_def{L}(char *s) = \strlen(s);

    // Predicate to check if a substring from index `start` to `end`
    // (inclusive) starts and ends with the same character.
    predicate same_char_ends(char *s, integer start, integer end) =
      @  0 <= start && start <= end && end < string_length(s) &&
      @  s[start] == s[end];

    // Recursive logic function to count substrings satisfying `same_char_ends`
    // within a given range [start_idx, end_idx].
    logic integer count_same_char_ends_recursive(char *s, integer start_idx, integer end_idx);

    // Base case: If start_idx is greater than end_idx, no substrings in this range.
    axiom count_same_char_ends_recursive_base_empty{L}:
      \forall char *s, integer start_idx, integer end_idx;
        start_idx > end_idx ==> count_same_char_ends_recursive(s, start_idx, end_idx) == 0;

    // Base case: If start_idx equals end_idx, one substring (the character itself),
    // which always starts and ends with the same character.
    axiom count_same_char_ends_recursive_base_single{L}:
      \forall char *s, integer start_idx;
        count_same_char_ends_recursive(s, start_idx, start_idx) == 1;

    // Recursive step:
    // Count for [start_idx, end_idx] is:
    //   - count for [start_idx, end_idx - 1] (subproblems not ending at end_idx)
    //   - plus 1 if the substring [start_idx, end_idx] itself satisfies the condition
    //   - plus count for [start_idx + 1, end_idx] (subproblems not starting at start_idx)
    //   - minus count for [start_idx + 1, end_idx - 1] (to avoid double counting)
    // This is the standard inclusion-exclusion principle for counting substrings.
    // However, a simpler iteration is usually preferred for implementation.
    // Let's redefine `count_same_char_ends_recursive` to reflect the sum of counts
    // for all `j` from `i` to `n-1` where `s[i] == s[j]`.

    // A more direct recursive definition for counting all substrings (i,j) where i <= j
    // and s[i] == s[j].
    // This definition mirrors the nested loop structure of the C code.
    logic integer count_all_same_char_ends(char *s, integer n);

    axiom count_all_same_char_ends_base{L}:
      \forall char *s, integer n;
        n <= 0 ==> count_all_same_char_ends(s, n) == 0;

    axiom count_all_same_char_ends_recursive_step{L}:
      \forall char *s, integer n;
        n > 0 ==> count_all_same_char_ends(s, n) ==
          count_all_same_char_ends(s, n - 1) + // Count for string up to n-2
          (\sum integer j; 0 <= j < n; (if s[j] == s[n-1] then 1 else 0)); // Add counts for substrings ending at n-1
  }
*/

/*@
  requires \valid_read(s);
  requires \strlen(s) >= 0;
  assigns \nothing;
  // Rule II.3: Use logical equivalence for boolean-like return values.
  ensures \result == count_all_same_char_ends(s, \strlen(s));
*/
int count_same_char_substrings(char *s) {
    int count = 0;
    int n = 0;

    // Calculate string length manually since we can't use strlen from <string.h>
    /*@
      loop invariant 0 <= n <= \strlen(s);
      loop invariant \forall integer k; 0 <= k < n ==> s[k] != '\0';
      loop assigns n;
      loop variant \strlen(s) - n;
    */
    while (s[n] != '\0') {
        n++;
    }

    /*@
      loop invariant 0 <= i <= n;
      loop invariant count == (\sum integer k; 0 <= k < i; (\sum integer l; k <= l < n; (if s[k] == s[l] then 1 else 0)));
      loop assigns i, count;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i <= j <= n;
          loop invariant count == (\sum integer k; 0 <= k < i; (\sum integer l; k <= l < n; (if s[k] == s[l] then 1 else 0))) +
                                 (\sum integer l; i <= l < j; (if s[i] == s[l] then 1 else 0));
          loop assigns j, count;
          loop variant n - j;
        */
        for (int j = i; j < n; j++) {
            if (s[i] == s[j]) {
                count++;
            }
        }
    }
    return count;
}
