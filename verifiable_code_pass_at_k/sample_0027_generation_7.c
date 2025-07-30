// Task ID: 27
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Define recursive logic for complex properties.
  axiomatic HasDigit {
    logic boolean has_digit_char(char c);

    axiom has_digit_char_0: has_digit_char('0') == \true;
    axiom has_digit_char_1: has_digit_char('1') == \true;
    axiom has_digit_char_2: has_digit_char('2') == \true;
    axiom has_digit_char_3: has_digit_char('3') == \true;
    axiom has_digit_char_4: has_digit_char('4') == \true;
    axiom has_digit_char_5: has_digit_char('5') == \true;
    axiom has_digit_char_6: has_digit_char('6') == \true;
    axiom has_digit_char_7: has_digit_char('7') == \true;
    axiom has_digit_char_8: has_digit_char('8') == \true;
    axiom has_digit_char_9: has_digit_char('9') == \true;
    axiom has_digit_char_other: \forall char c; !(c >= '0' && c <= '9') ==> has_digit_char(c) == \false;

    logic boolean has_digit_string(char *s, int len);

    axiom has_digit_string_empty: has_digit_string(s, 0) == \false;
    axiom has_digit_string_recursive:
      \forall char *s, integer len;
        len > 0 ==> (has_digit_string(s, len) == (has_digit_char(s[len-1]) || has_digit_string(s, len-1)));
  }

  // Rule II.1, II.2: Recursive logic for string equality after digit removal.
  axiomatic StringNoDigitsEq {
    logic char get_char_if_not_digit(char c);
    axiom get_char_if_not_digit_digit: \forall char c; (c >= '0' && c <= '9') ==> (get_char_if_not_digit(c) == '\0');
    axiom get_char_if_not_digit_nondigit: \forall char c; !(c >= '0' && c <= '9') ==> (get_char_if_not_digit(c) == c);

    logic integer count_nondigits(char *s, integer len);
    axiom count_nondigits_empty: count_nondigits(s, 0) == 0;
    axiom count_nondigits_recursive:
      \forall char *s, integer len;
        len > 0 ==> (count_nondigits(s, len) == (count_nondigits(s, len-1) + (has_digit_char(s[len-1]) ? 0 : 1)));

    logic char get_nondigit_at_index(char *s, integer len, integer k);
    axiom get_nondigit_at_index_def:
      \forall char *s, integer len, integer k;
        0 <= k < count_nondigits(s, len) ==>
        \exists integer i; 0 <= i < len &&
          (get_char_if_not_digit(s[i]) != '\0') &&
          (count_nondigits(s, i) == k) &&
          (get_nondigit_at_index(s, len, k) == s[i]);

    // This logic function represents the string after digits are removed
    // It's effectively a sequence of characters.
    logic char char_at_no_digits(char *s, integer s_len, integer k);
    axiom char_at_no_digits_def:
      \forall char *s, integer s_len, integer k;
        0 <= k < count_nondigits(s, s_len) ==>
        char_at_no_digits(s, s_len, k) == get_nondigit_at_index(s, s_len, k);

    // This logic function checks if two strings are equal after digits are removed from the first
    logic boolean string_equal_no_digits(char *src, integer src_len, char *dest, integer dest_len);
    axiom string_equal_no_digits_def:
      \forall char *src, integer src_len, char *dest, integer dest_len;
        string_equal_no_digits(src, src_len, dest, dest_len) <==>
        (count_nondigits(src, src_len) == dest_len &&
         \forall integer k; 0 <= k < dest_len ==> char_at_no_digits(src, src_len, k) == dest[k]);
  }
*/

/*@
  requires \valid_read(src+(0..src_len-1));
  requires \valid_write(dest+(0..dest_len-1));
  requires src_len >= 0;
  requires dest_len >= 0;
  // Rule II.5: Ensure dest has enough space.
  requires dest_len >= count_nondigits(src, src_len);

  assigns dest[0..dest_len-1];

  // Rule II.3: Ensures clause for boolean-like function (implicit return of string via dest).
  // The function effectively "returns" the modified string in `dest`.
  ensures string_equal_no_digits(src, src_len, dest, \result);
  ensures \result == count_nondigits(src, src_len);
*/
int remove_digits_from_string(char *src, int src_len, char *dest, int dest_len) {
    int dest_idx = 0;
    /*@
      loop invariant 0 <= i <= src_len;
      loop invariant 0 <= dest_idx <= i;
      loop invariant \forall integer k; 0 <= k < dest_idx ==> has_digit_char(dest[k]) == \false;
      loop invariant string_equal_no_digits(src, i, dest, dest_idx);
      loop assigns i, dest_idx, dest[0..dest_idx-1];
      loop variant src_len - i;
    */
    for (int i = 0; i < src_len; i++) {
        // Rule II.5: Prevent potential out-of-bounds access for dest if pre-condition is violated.
        // This is covered by the requires clause: dest_len >= count_nondigits(src, src_len)
        // and the loop invariant: dest_idx <= i <= src_len
        if (!(src[i] >= '0' && src[i] <= '9')) { // Check if it's not a digit
            dest[dest_idx] = src[i];
            dest_idx++;
        }
    }
    return dest_idx; // Return the new length of the string
}

/*@
  requires num_strings >= 0;
  requires max_string_len >= 0;
  // Rule I.3: Array pointer decay.
  requires \valid_read(strings_in);
  requires \valid_read(strings_in[0..num_strings-1]);
  requires \forall integer i; 0 <= i < num_strings ==> \valid_read(strings_in[i] + (0..max_string_len-1));
  requires \valid_write(strings_out);
  requires \valid_write(strings_out[0..num_strings-1]);
  requires \forall integer i; 0 <= i < num_strings ==> \valid_write(strings_out[i] + (0..max_string_len-1));

  assigns strings_out[0..num_strings-1][0..max_string_len-1];

  ensures \forall integer i; 0 <= i < num_strings ==>
    string_equal_no_digits(strings_in[i], max_string_len, strings_out[i], \result[i]);
  ensures \forall integer i; 0 <= i < num_strings ==>
    \result[i] == count_nondigits(strings_in[i], max_string_len);
  ensures \result == num_strings; // Returns the number of strings processed (implicitly via output array).
*/
void remove_digits_from_list(char strings_in[][256], int strings_in_len[], char strings_out[][256], int num_strings, int max_string_len, int strings_out_len_actual[]) {
    /*@
      loop invariant 0 <= i <= num_strings;
      loop invariant \forall integer k; 0 <= k < i ==>
        string_equal_no_digits(strings_in[k], strings_in_len[k], strings_out[k], strings_out_len_actual[k]);
      loop invariant \forall integer k; 0 <= k < i ==>
        strings_out_len_actual[k] == count_nondigits(strings_in[k], strings_in_len[k]);
      loop assigns i, strings_out[0..num_strings-1][0..max_string_len-1], strings_out_len_actual[0..num_strings-1];
      loop variant num_strings - i;
    */
    for (int i = 0; i < num_strings; i++) {
        // Assume strings_in_len[i] is the actual length of the string at index i.
        // For simplicity and to match the problem statement's "list of strings",
        // we'll use max_string_len as the buffer size and assume strings are null-terminated or have known length.
        // Here, we'll use strings_in_len[i] as the actual length of the current string.
        strings_out_len_actual[i] = remove_digits_from_string(strings_in[i], strings_in_len[i], strings_out[i], max_string_len);
        // Ensure null termination for the output string, assuming it's a C-style string.
        // This is important for usability but not strictly part of the "remove digits" logic.
        // We ensure `max_string_len` is large enough to hold the result + null terminator.
        // For this problem, we assume `max_string_len` is the buffer size.
        // If `strings_out_len_actual[i]` is less than `max_string_len`, we can null-terminate.
        /*@
          requires strings_out_len_actual[i] < max_string_len;
          assigns strings_out[i][strings_out_len_actual[i]];
          ensures strings_out[i][strings_out_len_actual[i]] == '\0';
        */
        if (strings_out_len_actual[i] < max_string_len) {
            strings_out[i][strings_out_len_actual[i]] = '\0';
        }
    }
}
