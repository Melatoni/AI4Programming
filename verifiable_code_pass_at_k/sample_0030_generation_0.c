// Task ID: 30
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled for string.

  // Rule II.1, II.2: Define a logic function to represent the property of a substring.
  // This is a helper for the main logic.
  axiomatic SubstringProperty {
    logic boolean is_substring_valid(char *s, int start, int end, int len);

    // Axiom for an empty or single-character substring (always valid)
    axiom is_substring_valid_base:
      \forall char *s, integer start, integer end, integer len;
        0 <= start <= end < len ==>
        (start == end || start + 1 == end) ==>
        is_substring_valid(s, start, end, len);

    // Axiom for a multi-character substring
    axiom is_substring_valid_recursive:
      \forall char *s, integer start, integer end, integer len;
        0 <= start < end < len ==>
        (s[start] == s[end]) ==>
        is_substring_valid(s, start, end, len);

    // Helper axiom: If a substring is valid, its start char matches its end char.
    // This is implicitly captured by the recursive axiom, but can be useful for prover.
    // However, for this problem, the condition `s[start] == s[end]` is the *definition*
    // we are counting. So, we define a logic predicate directly for that.
    logic boolean is_counted_substring(char *s, int start, int end, int len) =
      0 <= start <= end < len && s[start] == s[end];

    // Helper axiom for the count. This is how we will define the total count.
    logic integer count_valid_substrings(char *s, int len);

    axiom count_valid_substrings_base:
      \forall char *s, integer len;
        len == 0 ==> count_valid_substrings(s, len) == 0;

    axiom count_valid_substrings_recursive:
      \forall char *s, integer len;
        len > 0 ==>
        count_valid_substrings(s, len) ==
        (count_valid_substrings(s, len - 1) +
         (\sum integer i; 0 <= i < len;
            (if is_counted_substring(s, i, len - 1, len) then 1 else 0)));
  }
*/

/*@
  // Rule II.5: Prevent runtime errors.
  // The string must be null-terminated and its length must be within int limits.
  // For simplicity, we assume `len` is the actual length without the null terminator.
  requires \valid(s + (0..len)); // s[len] must be '\0'
  requires s[len] == '\0';
  requires len >= 0;
  // No overflow for count, assuming `len` is not excessively large.
  // Max possible count for len 'L' is L * (L + 1) / 2.
  // For L = 65535, L*(L+1)/2 is approx 2 * 10^9, fits in int.
  // For L = 46340, L*(L+1)/2 is approx 10^9.
  // Let's set a practical limit to prevent overflow, e.g., max len for int result.
  requires len <= 65535; // This ensures count_valid_substrings will not overflow int.

  assigns \nothing;

  // Rule II.3: The ensures clause uses logical equivalence.
  // The result must be exactly the count_valid_substrings as defined in ACSL.
  ensures \result == count_valid_substrings(s, len);
*/
int count_substrings_same_char(char *s, int len) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= len;
      // The outer loop invariant captures the count accumulated so far.
      loop invariant count == (\sum integer k; 0 <= k < i;
                                (\sum integer j; k <= j < len;
                                  (if is_counted_substring(s, k, j, len) then 1 else 0)));
      // More precise: count is the total for substrings starting at index < i.
      loop invariant count == (\sum integer start_idx; 0 <= start_idx < i;
                                (\sum integer end_idx; start_idx <= end_idx < len;
                                  (if s[start_idx] == s[end_idx] then 1 else 0)));

      loop assigns i, count;
      // Rule II.4: Loop variant for termination.
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        /*@
          loop invariant i <= j <= len;
          // The inner loop invariant captures the count for substrings starting at 'i'.
          loop invariant count == (\at(count, LoopEntry) +
                                    (\sum integer k; i <= k < j;
                                      (if s[i] == s[k] then 1 else 0)));
          loop assigns j, count;
          loop variant len - j;
        */
        for (int j = i; j < len; j++) {
            // Rule I.2: Using int for boolean logic.
            if (s[i] == s[j]) {
                count++;
            }
        }
    }
    return count;
}
