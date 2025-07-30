// Task ID: 18
// Generation: 0

/*@
  // Axiomatic block for recursive logic and helper axioms.
  // Rule II.1: Using axiomatic for complex logic.
  axiomatic CharInString {
    // Defines if a character 'c' is present in a string 's' of length 'len'.
    logic boolean char_in_string_rec(char c, char* s, int len);

    // Base case: empty string
    axiom char_in_string_rec_base:
      \forall char c, char* s; char_in_string_rec(c, s, 0) == \false;

    // Recursive case:
    axiom char_in_string_rec_rec:
      \forall char c, char* s, integer len; len > 0 ==>
        char_in_string_rec(c, s, len) == (s[len-1] == c || char_in_string_rec(c, s, len-1));

    // Helper axiom: If char is in string, it must be at some index.
    // Rule II.2: CRITICAL - Helper Axioms.
    axiom char_in_string_helper_exists:
      \forall char c, char* s, integer len;
        char_in_string_rec(c, s, len) <==> (\exists integer i; 0 <= i < len && s[i] == c);
  }
*/

/*@
  requires \valid_read(s1 + (0..len1-1));
  requires \valid_read(s2 + (0..len2-1));
  requires len1 >= 0;
  requires len2 >= 0;
  requires \valid(result + (0..len1-1)); // 'result' can be at most 'len1' long
  requires result != s1; // No aliasing between input and output string
  requires result != s2; // No aliasing between input and filter string

  assigns result[0..len1-1];

  // The 'ensures' clause defines the post-condition for the function.
  // Rule II.3: Use logical equivalence for boolean-like functions.
  ensures \forall integer k; 0 <= k < \result ==>
    s1[k] == result[k] || char_in_string_rec(s1[k], s2, len2) || (\exists integer j; 0 <= j < k && char_in_string_rec(s1[j], s2, len2) && s1[j] == s1[k]);

  ensures \forall integer k; 0 <= k < \result ==>
    !char_in_string_rec(result[k], s2, len2);

  ensures \forall integer k; 0 <= k < len1 ==>
    (char_in_string_rec(s1[k], s2, len2) || (\exists integer j; 0 <= j < k && char_in_string_rec(s1[j], s2, len2))) <==> !(\exists integer l; 0 <= l < \result && result[l] == s1[k]);

  ensures \result <= len1;
*/
int remove_chars(char* s1, int len1, char* s2, int len2, char* result) {
    int write_idx = 0;
    /*@
      loop invariant 0 <= read_idx <= len1;
      loop invariant 0 <= write_idx <= read_idx;
      // All characters processed so far that are NOT in s2 have been copied to 'result'.
      loop invariant \forall integer k; 0 <= k < read_idx ==>
        (char_in_string_rec(s1[k], s2, len2) <==> !(\exists integer j; 0 <= j < write_idx && result[j] == s1[k]));

      // All characters currently in 'result' are from 's1' and are not in 's2'.
      loop invariant \forall integer k; 0 <= k < write_idx ==>
        !char_in_string_rec(result[k], s2, len2) && (\exists integer j; 0 <= j < read_idx && s1[j] == result[k]);

      loop assigns read_idx, write_idx, result[0..len1-1];
      loop variant len1 - read_idx;
    */
    for (int read_idx = 0; read_idx < len1; read_idx++) {
        int found_in_s2 = 0; // Rule I.2: Use int for boolean.
        /*@
          loop invariant 0 <= j <= len2;
          loop invariant found_in_s2 == (\exists integer k; 0 <= k < j && s2[k] == s1[read_idx]);
          loop assigns j, found_in_s2;
          loop variant len2 - j;
        */
        for (int j = 0; j < len2; j++) {
            if (s1[read_idx] == s2[j]) {
                found_in_s2 = 1; // Rule I.2: Use int for boolean.
                break;
            }
        }

        if (found_in_s2 == 0) { // Rule I.2: Use int for boolean.
            result[write_idx] = s1[read_idx];
            write_idx++;
        }
    }
    return write_idx;
}
