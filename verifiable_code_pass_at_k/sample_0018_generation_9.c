// Task ID: 18
// Generation: 9

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Use int for booleans.

  // Axiomatic block for character presence in a string.
  // Rule II.1: Using recursive logic for complexity.
*/
/*@ axiomatic CharPresence {
  logic boolean is_char_present(char *s, int len, char c);

  axiom is_char_present_empty{
    \forall char *s, char c;
      is_char_present(s, 0, c) == \false;
  }

  axiom is_char_present_recursive{
    \forall char *s, int len, char c;
      len > 0 ==> is_char_present(s, len, c) == (s[0] == c || is_char_present(s + 1, len - 1, c));
  }

  // Rule II.2: Helper axiom to prove if a char is not present in a string.
  // This helps the prover when reasoning about `!is_char_present`.
  axiom is_char_not_present_implies_no_match {
    \forall char *s, int len, char c;
      !is_char_present(s, len, c) ==> (\forall integer i; 0 <= i < len ==> s[i] != c);
  }
}
*/

/*@
  requires \valid_read(str1 + (0..len1-1));
  requires \valid_read(str2 + (0..len2-1));
  requires \separated(str1 + (0..len1-1), str2 + (0..len2-1));
  requires len1 >= 0;
  requires len2 >= 0;

  // The function modifies str1 in place.
  assigns str1[0..len1-1];

  // Rule II.3: Ensures clause for boolean-like function (implicitly, as it modifies in place).
  // The result is the new length of str1.
  // Each character in the modified str1 must not be present in the original str2.
  // The order of characters not in str2 must be preserved.

  ensures \result >= 0 && \result <= len1;
  ensures \forall integer i; 0 <= i < \result ==> !is_char_present(str2, len2, str1[i]);
  ensures \forall integer i, j; 0 <= i < j < \result ==>
                                (\exists integer k1, k2;
                                 0 <= k1 < k2 < len1 &&
                                 str1[i] == \old(str1[k1]) &&
                                 str1[j] == \old(str1[k2]) &&
                                 !is_char_present(str2, len2, \old(str1[k1])) &&
                                 !is_char_present(str2, len2, \old(str1[k2])));

  // The characters that are not removed must appear in the same relative order.
  ensures \forall integer i; 0 <= i < \result ==>
          (\exists integer k; 0 <= k < len1 &&
           str1[i] == \old(str1[k]) &&
           !is_char_present(str2, len2, \old(str1[k])) &&
           (\forall integer j; 0 <= j < i ==>
            (\exists integer p; 0 <= p < k && str1[j] == \old(str1[p]))));
*/
int remove_chars(char *str1, int len1, char *str2, int len2) {
    int write_idx = 0;
    /*@
      loop invariant 0 <= write_idx <= read_idx <= len1;

      // Invariant: all characters written so far are not in str2.
      loop invariant \forall integer i; 0 <= i < write_idx ==> !is_char_present(str2, len2, str1[i]);

      // Invariant: all characters from original str1 up to read_idx that are not in str2
      // have been copied to str1[0..write_idx-1] in their original relative order.
      loop invariant \forall integer i; 0 <= i < write_idx ==>
          (\exists integer k; 0 <= k < read_idx &&
           str1[i] == \old(str1[k]) &&
           !is_char_present(str2, len2, \old(str1[k])) &&
           (\forall integer j; 0 <= j < i ==>
            (\exists integer p; 0 <= p < k && str1[j] == \old(str1[p]))));

      // Invariant: The content of str1 up to write_idx is final for this loop iteration.
      loop invariant \forall integer k; 0 <= k < write_idx ==> str1[k] == \at(str1[k], LoopEntry);

      loop assigns write_idx, str1[0..len1-1];
      loop variant len1 - read_idx;
    */
    for (int read_idx = 0; read_idx < len1; read_idx++) {
        char current_char = str1[read_idx];
        int found_in_str2 = 0; // Rule I.2: Use int for boolean.

        /*@
          loop invariant 0 <= j <= len2;
          loop invariant found_in_str2 == 0 ==> (\forall integer k; 0 <= k < j ==> str2[k] != current_char);
          loop invariant found_in_str2 == 1 ==> (\exists integer k; 0 <= k < j && str2[k] == current_char);
          loop assigns found_in_str2, j;
          loop variant len2 - j;
        */
        for (int j = 0; j < len2; j++) {
            if (current_char == str2[j]) {
                found_in_str2 = 1;
                break;
            }
        }

        if (found_in_str2 == 0) {
            str1[write_idx] = current_char;
            write_idx++;
        }
    }
    return write_idx;
}
