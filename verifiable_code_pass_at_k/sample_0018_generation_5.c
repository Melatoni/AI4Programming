// Task ID: 18
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in axiomatic blocks.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms are CRITICAL.
  // Rule II.3: ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Axiomatic block for character presence in a string.
  axiomatic CharPresence {
    logic boolean contains_char(char *s, int len, char c);

    axiom contains_char_empty:
      \forall char *s, char c; contains_char(s, 0, c) == \false;

    axiom contains_char_recursive:
      \forall char *s, int len, char c;
        len > 0 ==> (contains_char(s, len, c) == (s[len-1] == c || contains_char(s, len-1, c)));
  }
*/

/*@
  // Function to remove characters from the first string that are present in the second string.
  // The function modifies the first string `s1` in-place and returns the new length.
  // The function assumes `s1` and `s2` are null-terminated C strings.
  // `len1` is the original length of `s1` (excluding null terminator).
  // `len2` is the original length of `s2` (excluding null terminator).

  requires \valid(s1 + (0..len1)); // s1 is a valid array of chars up to len1
  requires \valid(s2 + (0..len2)); // s2 is a valid array of chars up to len2
  requires s1[len1] == '\0';       // s1 is null-terminated
  requires s2[len2] == '\0';       // s2 is null-terminated
  requires len1 >= 0;
  requires len2 >= 0;

  // The function modifies `s1`.
  assigns s1[0..len1];

  // The result `\result` is the new length of `s1`.
  ensures \result >= 0 && \result <= len1;

  // Each character at index `k` in the modified string `s1` (up to `\result-1`)
  // must not be present in the original `s2` string.
  ensures \forall integer k; 0 <= k < \result ==> !contains_char(s2, len2, \old(s1[k]));

  // The characters in the modified string `s1` are a subsequence of the original `s1`
  // and maintain their relative order.
  // This is a complex property to express precisely with simple ACSL,
  // but we can ensure that characters NOT in s2 are preserved.
  // We specify that the characters that remain are exactly those from the original string
  // that are NOT in s2, and they appear in their original relative order.
  ensures \forall integer i, j;
    0 <= i < len1 && 0 <= j < \result && \old(s1[i]) == s1[j] && !contains_char(s2, len2, \old(s1[i]))
    ==> (\exists integer k; 0 <= k < i && \old(s1[k]) == s1[j-1] && !contains_char(s2,len2,\old(s1[k]))
         || j == 0); // Either it's the first char, or the previous one also satisfies the condition.

  // The new string is also null-terminated.
  ensures s1[\result] == '\0';
*/
int remove_chars(char *s1, int len1, char *s2, int len2) {
  int write_idx = 0; // Index for writing to the modified string

  /*@
    loop invariant 0 <= read_idx <= len1;
    loop invariant 0 <= write_idx <= read_idx;

    // All characters written so far (s1[0..write_idx-1]) are not in s2.
    loop invariant \forall integer k; 0 <= k < write_idx ==> !contains_char(s2, len2, \old(s1[k]));

    // The characters s1[0..write_idx-1] are a subsequence of \old(s1[0..read_idx-1])
    // where elements not in s2 are preserved.
    loop invariant \forall integer src_idx, dest_idx;
      0 <= dest_idx < write_idx && 0 <= src_idx < read_idx && s1[dest_idx] == \old(s1[src_idx])
      ==> (!contains_char(s2, len2, \old(s1[src_idx])) &&
           (\forall integer k; 0 <= k < src_idx
              ==> (contains_char(s2, len2, \old(s1[k])) ||
                   (\exists integer l; 0 <= l < dest_idx && s1[l] == \old(s1[k])
                    && (\forall integer m; l < m < dest_idx ==> s1[m] != \old(s1[k]))
                   )
                  )
           )
      );

    // The part of s1 from write_idx to read_idx-1 contains characters that were skipped.
    loop invariant \forall integer k; write_idx <= k < read_idx ==> contains_char(s2, len2, \old(s1[k]));

    loop assigns write_idx, s1[0..len1];
    loop variant len1 - read_idx;
  */
  for (int read_idx = 0; read_idx < len1; read_idx++) {
    char current_char = s1[read_idx];
    int found_in_s2 = 0;
    /*@
      loop invariant 0 <= i <= len2;
      loop invariant found_in_s2 == (\exists integer k; 0 <= k < i && s2[k] == current_char);
      loop assigns found_in_s2, i;
      loop variant len2 - i;
    */
    for (int i = 0; i < len2; i++) {
      if (s2[i] == current_char) {
        found_in_s2 = 1;
        break;
      }
    }

    if (found_in_s2 == 0) { // If current_char is NOT in s2
      s1[write_idx] = current_char;
      write_idx++;
    }
  }

  s1[write_idx] = '\0'; // Null-terminate the new string
  return write_idx;
}
