// Task ID: 18
// Generation: 6

/*@
  // Axiomatic block for character presence in a string
  axiomatic CharPresence {
    logic boolean is_char_in_string(char c, char* s, int len);

    // Rule II.1: Base case for recursive logic
    axiom is_char_in_string_empty{
      \forall char c, char* s;
        is_char_in_string(c, s, 0) == \false;
    }

    // Rule II.1: Recursive case for recursive logic
    axiom is_char_in_string_recursive{
      \forall char c, char* s, integer len;
        len > 0 ==>
        (is_char_in_string(c, s, len) == (c == s[0] || is_char_in_string(c, s + 1, len - 1)));
    }
  }
*/

/*@
  requires \valid_read(str1 + (0..len1-1));
  requires \valid_read(str2 + (0..len2-1));
  requires len1 >= 0;
  requires len2 >= 0;
  requires \valid(str_out + (0..len1-1)); // str_out must be large enough to hold the result

  assigns str_out[0..len1-1];

  // Rule II.3: Ensures clause for boolean-like function (implicit in the output string content)
  // The result (str_out) contains only characters from str1 that are NOT in str2.
  ensures \forall integer k; 0 <= k < \result ==>
          str_out[k] == \old(str1[\at(index1, Post_loop_outer)[k]]) &&
          !is_char_in_string(str_out[k], \old(str2), len2);

  // The length of the output string is the number of characters from str1 not in str2.
  ensures \result == (\sum integer i; 0 <= i < len1 && !is_char_in_string(\old(str1[i]), \old(str2), len2));

  // No characters are lost from str1 that should be preserved.
  ensures \forall integer i; 0 <= i < len1 && !is_char_in_string(\old(str1[i]), \old(str2), len2) ==>
          (\exists integer k; 0 <= k < \result && str_out[k] == \old(str1[i]));

  // The characters in str_out maintain their original relative order from str1.
  ensures \forall integer k1, k2; 0 <= k1 < k2 < \result ==>
          \at(index1, Post_loop_outer)[k1] < \at(index1, Post_loop_outer)[k2];
*/
int remove_chars(char* str1, int len1, char* str2, int len2, char* str_out) {
    int out_idx = 0; // Current index for the output string

    /*@
      loop invariant 0 <= i <= len1;
      loop invariant 0 <= out_idx <= i;

      // All characters processed so far from str1 that are not in str2 are correctly copied to str_out.
      loop invariant \forall integer k; 0 <= k < out_idx ==>
                     str_out[k] == \at(str1, Pre)[ \at(index1, LoopCurrent)[k] ] &&
                     !is_char_in_string(str_out[k], \at(str2, Pre), \at(len2, Pre));

      // The length of str_out so far is exactly the count of characters from str1[0..i-1] not in str2.
      loop invariant out_idx == (\sum integer k; 0 <= k < i && !is_char_in_string(\at(str1, Pre)[k], \at(str2, Pre), \at(len2, Pre)));

      // The relative order of characters in str_out is preserved.
      loop invariant \forall integer k1, k2; 0 <= k1 < k2 < out_idx ==>
                     \at(index1, LoopCurrent)[k1] < \at(index1, LoopCurrent)[k2];

      loop assigns i, out_idx, str_out[0..len1-1];
      loop variant len1 - i;
    */
    for (int i = 0; i < len1; i++) {
        char current_char = str1[i];
        int found_in_str2 = 0; // Rule I.2: Use int for boolean

        /*@
          loop invariant 0 <= j <= len2;
          loop invariant found_in_str2 == 0 ==>
                         \forall integer k; 0 <= k < j ==> current_char != \at(str2, Pre)[k];
          loop invariant found_in_str2 == 1 ==>
                         (\exists integer k; 0 <= k < j && current_char == \at(str2, Pre)[k]);

          loop assigns j, found_in_str2;
          loop variant len2 - j;
        */
        for (int j = 0; j < len2; j++) {
            if (current_char == str2[j]) {
                found_in_str2 = 1;
                break;
            }
        }

        if (found_in_str2 == 0) { // If character not found in str2
            str_out[out_idx] = current_char;
            //@ ghost \at(index1, LoopCurrent)[out_idx] = i; // Store original index for postconditions
            out_idx++;
        }
    }

    return out_idx;
}
