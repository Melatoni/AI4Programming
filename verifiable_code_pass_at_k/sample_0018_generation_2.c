// Task ID: 18
// Generation: 2

/*@
  // Axiomatic block for recursive logic and helper axioms (Rule II.1, II.2)
  axiomatic CharSet {
    // Defines whether a character 'c' is present in the first 'len_s' characters of string 's'.
    logic boolean is_char_in_string(char c, char *s, int len_s);

    axiom is_char_in_string_empty:
      \forall char c, char *s;
        is_char_in_string(c, s, 0) == \false;

    axiom is_char_in_string_rec:
      \forall char c, char *s, integer len_s;
        len_s > 0 ==>
        is_char_in_string(c, s, len_s) == (s[len_s - 1] == c || is_char_in_string(c, s, len_s - 1));

    // Helper axiom: If a character is in a string, it must be at some index.
    axiom is_char_in_string_exists:
      \forall char c, char *s, integer len_s;
        is_char_in_string(c, s, len_s) <==> (\exists integer i; 0 <= i < len_s && s[i] == c);
  }
*/

/*@
  requires \valid(str1 + (0..len1-1));
  requires \valid(str2 + (0..len2-1));
  requires len1 >= 0;
  requires len2 >= 0;
  requires \separated(str1 + (0..len1-1), str2 + (0..len2-1));

  // The function modifies str1 in place.
  assigns str1[0..len1-1];

  // The ensures clause describes the post-condition of the modified str1.
  // It states that the new length 'result' is correct, and all characters
  // up to 'result' are those from the original str1 that were not in str2.
  ensures \result >= 0 && \result <= len1;
  ensures \forall integer i; 0 <= i < \result ==>
    (\exists integer j; 0 <= j < len1 && \old(str1[j]) == str1[i] && !is_char_in_string(\old(str1[j]), str2, len2));
  ensures \forall integer i; 0 <= i < len1 ==>
    (is_char_in_string(\old(str1[i]), str2, len2) ==>
      !\exists integer k; 0 <= k < \result && str1[k] == \old(str1[i]));
  ensures \forall integer i; 0 <= i < len1 && !is_char_in_string(\old(str1[i]), str2, len2) ==>
    (\exists integer k; 0 <= k < \result && str1[k] == \old(str1[i]));
  ensures \forall integer i, j; 0 <= i < j < \result ==>
    (\exists integer k, l; 0 <= k < l < len1 && \old(str1[k]) == str1[i] && \old(str1[l]) == str1[j] &&
     !is_char_in_string(\old(str1[k]), str2, len2) && !is_char_in_string(\old(str1[l]), str2, len2));
*/
int remove_chars(char *str1, int len1, char *str2, int len2) {
    int write_idx = 0; // Index for writing to the modified string

    /*@
      loop invariant 0 <= read_idx <= len1;
      loop invariant 0 <= write_idx <= read_idx;

      // All characters written so far are from original str1 and not in str2.
      loop invariant \forall integer k; 0 <= k < write_idx ==>
        (\exists integer j; 0 <= j < read_idx && \at(str1[j], Pre) == str1[k] && !is_char_in_string(str1[k], str2, len2));

      // No character that should be removed has been written.
      loop invariant \forall integer k; 0 <= k < write_idx ==>
        !is_char_in_string(str1[k], str2, len2);

      // The part of str1 beyond write_idx is not yet processed.
      loop invariant \forall integer k; write_idx <= k < read_idx ==>
        str1[k] == \at(str1[k], Pre);

      loop assigns write_idx, str1[0..len1-1], read_idx;
      loop variant len1 - read_idx;
    */
    for (int read_idx = 0; read_idx < len1; read_idx++) {
        char current_char = str1[read_idx];

        // Check if current_char is present in str2
        int found_in_str2 = 0; // Rule I.2: Use int for boolean
        /*@
          loop invariant 0 <= i <= len2;
          loop invariant found_in_str2 == 0 ==> \forall integer k; 0 <= k < i ==> str2[k] != current_char;
          loop invariant found_in_str2 == 1 ==> \exists integer k; 0 <= k < i && str2[k] == current_char;
          loop assigns found_in_str2, i;
          loop variant len2 - i;
        */
        for (int i = 0; i < len2; i++) {
            if (str2[i] == current_char) {
                found_in_str2 = 1;
                break;
            }
        }

        if (found_in_str2 == 0) { // If current_char is NOT in str2
            str1[write_idx] = current_char;
            write_idx++;
        }
    }

    // Null-terminate the modified string if it's a C-string.
    // This problem description implies a length, not necessarily null-termination,
    // so we return the new logical length. If null-termination was required,
    // "requires write_idx < len1 + 1" and "str1[write_idx] = '\0';" would be added.

    return write_idx;
}
