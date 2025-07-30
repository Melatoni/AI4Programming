// Task ID: 18
// Generation: 3

/*@
  // Axiomatic block for character presence in a string.
  // Rule II.1: Using recursive logic for complexity.
  axiomatic CharPresence {
    logic boolean is_char_present(char c, char *s, integer len);

    axiom is_char_present_empty:
      \forall char c, char *s; is_char_present(c, s, 0) == \false;

    axiom is_char_present_recursive:
      \forall char c, char *s, integer len;
      len > 0 ==> (is_char_present(c, s, len) == (s[len - 1] == c || is_char_present(c, s, len - 1)));

    // Rule II.2: Helper axiom for is_char_present to simplify proofs.
    // If a char is present, it must be at some index.
    axiom is_char_present_exists:
      \forall char c, char *s, integer len;
      is_char_present(c, s, len) <==> (\exists integer i; 0 <= i < len && s[i] == c);
  }
*/

/*@
  requires \valid_read(s1 + (0..len1-1));
  requires \valid_read(s2 + (0..len2-1));
  requires \valid(result + (0..len1-1));

  // The result string has at most the length of s1.
  requires len1 >= 0;
  requires len2 >= 0;

  assigns result[0..len1-1];

  // Rule II.3: Ensures clause using logical equivalence.
  // A character s1[k] is in result iff it's not present in s2.
  // And the order of characters is preserved.
  ensures \forall integer k; 0 <= k < \old(len1) ==>
            (is_char_present(\old(s1[k]), \old(s2), \old(len2)) <==> \forall integer j; 0 <= j < \result - 1 ==> result[j] != \old(s1[k]));

  // The length of the result string must be correctly returned.
  ensures \result >= 0;
  ensures \result <= len1;

  // Each character in the result must come from s1 and not be in s2.
  ensures \forall integer i; 0 <= i < \result ==>
            (\exists integer j; 0 <= j < len1 && result[i] == s1[j] && !is_char_present(s1[j], s2, len2));

  // The order of characters from s1 that are kept is preserved.
  ensures \forall integer i, k; 0 <= i < \result && 0 <= k < \result && i < k ==>
            (\exists integer orig_i, orig_k; 0 <= orig_i < len1 && 0 <= orig_k < len1 && orig_i < orig_k &&
             s1[orig_i] == result[i] && s1[orig_k] == result[k]);
*/
int remove_chars(char *s1, int len1, char *s2, int len2, char *result) {
    int write_idx = 0; // Current write position in the result string

    /*@
      loop invariant 0 <= i <= len1;
      loop invariant 0 <= write_idx <= i;

      // Rule II.4: Loop invariant for the result string construction.
      // Characters already processed (s1[0..i-1]):
      // If s1[k] (for k < i) is not in s2, it is in result[0..write_idx-1].
      loop invariant \forall integer k; 0 <= k < i ==>
                       (is_char_present(s1[k], s2, len2) <==>
                        (\forall integer j; 0 <= j < write_idx ==> result[j] != s1[k]));

      // Order of characters in result is preserved from s1.
      loop invariant \forall integer m, n; 0 <= m < write_idx && 0 <= n < write_idx && m < n ==>
                       (\exists integer orig_m, orig_n; 0 <= orig_m < i && 0 <= orig_n < i && orig_m < orig_n &&
                        s1[orig_m] == result[m] && s1[orig_n] == result[n]);

      // Characters in result[0..write_idx-1] are from s1 and not in s2.
      loop invariant \forall integer j; 0 <= j < write_idx ==>
                       (\exists integer k; 0 <= k < i && result[j] == s1[k] && !is_char_present(s1[k], s2, len2));

      loop assigns i, write_idx, result[0..len1-1];
      loop variant len1 - i;
    */
    for (int i = 0; i < len1; i++) {
        int char_found_in_s2 = 0; // Rule I.2: Use int for boolean

        /*@
          loop invariant 0 <= j <= len2;
          loop invariant char_found_in_s2 == (\exists integer k; 0 <= k < j && s2[k] == s1[i]);
          loop assigns j, char_found_in_s2;
          loop variant len2 - j;
        */
        for (int j = 0; j < len2; j++) {
            if (s1[i] == s2[j]) {
                char_found_in_s2 = 1; // True
                break;
            }
        }

        if (char_found_in_s2 == 0) { // If not found in s2
            result[write_idx] = s1[i];
            write_idx++;
        }
    }

    return write_idx; // Return the new length of the string
}
