// Task ID: 27
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms for recursive functions.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic CharProperties {
    logic int is_digit(char c);

    axiom is_digit_true{L}:
      \forall char c; ('0' <= c <= '9') ==> is_digit(c) == 1;

    axiom is_digit_false{L}:
      \forall char c; !('0' <= c <= '9') ==> is_digit(c) == 0;

    // Helper axiom: Property of a character being a digit is binary.
    axiom is_digit_binary{L}:
      \forall char c; (is_digit(c) == 0 || is_digit(c) == 1);
  }
*/

/*@
  axiomatic StringDigitCount {
    logic integer count_digits_in_string(char* s, integer len);

    axiom count_digits_in_string_base:
      \forall char* s; count_digits_in_string(s, 0) == 0;

    axiom count_digits_in_string_recursive:
      \forall char* s, integer len;
        len > 0 ==> count_digits_in_string(s, len) ==
          (is_digit(s[len - 1]) == 1 ? 1 : 0) + count_digits_in_string(s, len - 1);

    // Helper axiom: The count of digits is non-negative.
    axiom count_digits_in_string_non_negative{L}:
      \forall char* s, integer len;
        count_digits_in_string(s, len) >= 0;

    // Helper axiom: The count of digits is at most the length of the string.
    axiom count_digits_in_string_upper_bound{L}:
      \forall char* s, integer len;
        count_digits_in_string(s, len) <= len;
  }
*/

/*@
  requires \valid_read(s + (0..len-1));
  requires len >= 0;
  assigns \nothing;
  ensures \result == count_digits_in_string(s, len);
*/
int get_digit_count(char* s, int len) {
  int count = 0;
  /*@
    loop invariant 0 <= i <= len;
    loop invariant count == count_digits_in_string(s, i);
    loop assigns i, count;
    loop variant len - i;
  */
  for (int i = 0; i < len; i++) {
    if (s[i] >= '0' && s[i] <= '9') {
      count++;
    }
  }
  return count;
}

/*@
  requires \valid_read(src + (0..src_len-1));
  requires \valid_write(dest + (0..src_len-1)); // dest must be large enough
  requires src_len >= 0;
  assigns dest[0..src_len-1];

  // The number of non-digit characters in src == the length of the resulting string in dest.
  ensures \result == src_len - count_digits_in_string(src, src_len);

  // The content of dest are exactly the non-digit characters from src, in order.
  ensures \forall integer i; 0 <= i < \result ==>
    (is_digit(dest[i]) == 0);

  ensures \forall integer k; 0 <= k < src_len ==>
    (is_digit(src[k]) == 0 ==>
      \exists integer j; 0 <= j < \result && dest[j] == src[k] &&
        (\forall integer l; l < j ==> \exists integer m; m < k && is_digit(src[m]) == 0 && src[m] == dest[l]));

  // Ensure dest is null-terminated if src_len allows.
  // This is implicitly handled by the return value being the new length.
  // We don't guarantee null termination, just the content up to the new length.
*/
int remove_digits_from_string(char* src, int src_len, char* dest) {
  int dest_idx = 0;
  /*@
    loop invariant 0 <= i <= src_len;
    loop invariant 0 <= dest_idx <= i;
    loop invariant dest_idx == i - count_digits_in_string(src, i);

    // All characters copied to dest so far are non-digits.
    loop invariant \forall integer k; 0 <= k < dest_idx ==> (is_digit(dest[k]) == 0);

    // Characters in src up to i have been processed.
    // The content of dest[0..dest_idx-1] corresponds to non-digits in src[0..i-1].
    loop invariant \forall integer k; 0 <= k < i ==>
      (is_digit(src[k]) == 0 ==>
        \exists integer j; 0 <= j < dest_idx && dest[j] == src[k] &&
          (\forall integer l; l < j ==> \exists integer m; m < k && is_digit(src[m]) == 0 && src[m] == dest[l]));

    loop assigns i, dest_idx, dest[0..src_len-1];
    loop variant src_len - i;
  */
  for (int i = 0; i < src_len; i++) {
    if (!(src[i] >= '0' && src[i] <= '9')) { // Check if it's NOT a digit
      dest[dest_idx] = src[i];
      dest_idx++;
    }
  }
  return dest_idx; // Return the new length of the string
}

/*@
  axiomatic ListProperties {
    // Defines the total number of characters in all strings in the list.
    logic integer total_chars(char** list, integer* lengths, integer num_strings);

    axiom total_chars_base:
      \forall char** list, integer* lengths; total_chars(list, lengths, 0) == 0;

    axiom total_chars_recursive:
      \forall char** list, integer* lengths, integer num_strings;
        num_strings > 0 ==> total_chars(list, lengths, num_strings) ==
          lengths[num_strings - 1] + total_chars(list, lengths, num_strings - 1);

    // Helper axiom: total_chars is non-negative.
    axiom total_chars_non_negative{L}:
      \forall char** list, integer* lengths, integer num_strings;
        total_chars(list, lengths, num_strings) >= 0;

    // Defines the total number of digits in all strings in the list.
    logic integer total_digits_in_list(char** list, integer* lengths, integer num_strings);

    axiom total_digits_in_list_base:
      \forall char** list, integer* lengths; total_digits_in_list(list, lengths, 0) == 0;

    axiom total_digits_in_list_recursive:
      \forall char** list, integer* lengths, integer num_strings;
        num_strings > 0 ==> total_digits_in_list(list, lengths, num_strings) ==
          count_digits_in_string(list[num_strings - 1], lengths[num_strings - 1]) +
          total_digits_in_list(list, lengths, num_strings - 1);

    // Helper axiom: total_digits_in_list is non-negative.
    axiom total_digits_in_list_non_negative{L}:
      \forall char** list, integer* lengths, integer num_strings;
        total_digits_in_list(list, lengths, num_strings) >= 0;

    // Defines the total length of all strings after digit removal.
    logic integer total_new_length(char** list, integer* lengths, integer num_strings);

    axiom total_new_length_base:
      \forall char** list, integer* lengths; total_new_length(list, lengths, 0) == 0;

    axiom total_new_length_recursive:
      \forall char** list, integer* lengths, integer num_strings;
        num_strings > 0 ==> total_new_length(list, lengths, num_strings) ==
          (lengths[num_strings - 1] - count_digits_in_string(list[num_strings - 1], lengths[num_strings - 1])) +
          total_new_length(list, lengths, num_strings - 1);

    // Helper axiom: total_new_length is non-negative.
    axiom total_new_length_non_negative{L}:
      \forall char** list, integer* lengths, integer num_strings;
        total_new_length(list, lengths, num_strings) >= 0;

    // Helper axiom: Relation between total_new_length and total_chars/total_digits_in_list.
    axiom total_new_length_relation{L}:
      \forall char** list, integer* lengths, integer num_strings;
        total_new_length(list, lengths, num_strings) ==
        total_chars(list, lengths, num_strings) - total_digits_in_list(list, lengths, num_strings);
  }
*/

/*@
  requires num_strings >= 0;
  requires \valid_read(list + (0..num_strings-1));
  requires \valid_read(lengths + (0..num_strings-1));
  requires \valid_write(new_lengths + (0..num_strings-1));

  // Each string in the input list must be valid read.
  requires \forall integer i; 0 <= i < num_strings ==> \valid_read(list[i] + (0..lengths[i]-1));

  // Each destination string must be valid write and large enough.
  requires \forall integer i; 0 <= i < num_strings ==> \valid_write(new_list[i] + (0..lengths[i]-1));

  // The output list of pointers must be valid write.
  requires \valid_write(new_list + (0..num_strings-1));

  assigns new_list[0..num_strings-1], new_lengths[0..num_strings-1],
          \separated(list[0..num_strings-1], new_list[0..num_strings-1]); // Ensure no aliasing between input/output strings
  assigns \separated(lengths[0..num_strings-1], new_lengths[0..num_strings-1]); // Ensure no aliasing between input/output lengths

  // Ensures each string in new_list is the result of removing digits from the corresponding string in list.
  ensures \forall integer i; 0 <= i < num_strings ==>
    new_lengths[i] == lengths[i] - count_digits_in_string(list[i], lengths[i]);

  ensures \forall integer i; 0 <= i < num_strings ==>
    (\forall integer k; 0 <= k < new_lengths[i] ==> (is_digit(new_list[i][k]) == 0));

  ensures \forall integer i; 0 <= i < num_strings ==>
    (\forall integer k; 0 <= k < lengths[i] ==>
      (is_digit(list[i][k]) == 0 ==>
        \exists integer j; 0 <= j < new_lengths[i] && new_list[i][j] == list[i][k] &&
          (\forall integer l; l < j ==> \exists integer m; m < k && is_digit(list[i][m]) == 0 && list[i][m] == new_list[i][l])));

  // The function returns the total number of characters in the modified list.
  ensures \result == total_new_length(list, lengths, num_strings);
*/
int remove_digits_from_list_of_strings(char** list, int* lengths, int num_strings,
                                       char** new_list, int* new_lengths) {
  int total_chars_removed = 0;
  /*@
    loop invariant 0 <= i <= num_strings;
    loop invariant total_chars_removed == total_digits_in_list(list, lengths, i);

    // All strings processed so far have been correctly transformed.
    loop invariant \forall integer k; 0 <= k < i ==>
      new_lengths[k] == lengths[k] - count_digits_in_string(list[k], lengths[k]);

    loop invariant \forall integer k; 0 <= k < i ==>
      (\forall integer l; 0 <= l < new_lengths[k] ==> (is_digit(new_list[k][l]) == 0));

    loop invariant \forall integer k; 0 <= k < i ==>
      (\forall integer l; 0 <= l < lengths[k] ==>
        (is_digit(list[k][l]) == 0 ==>
          \exists integer j; 0 <= j < new_lengths[k] && new_list[k][j] == list[k][l] &&
            (\forall integer m; m < j ==> \exists integer n; n < l && is_digit(list[k][n]) == 0 && list[k][n] == new_list[k][m])));

    loop assigns i, total_chars_removed, new_lengths[0..num_strings-1], new_list[0..num_strings-1];
    loop variant num_strings - i;
  */
  for (int i = 0; i < num_strings; i++) {
    int current_string_original_len = lengths[i];
    char* current_src_string = list[i];
    char* current_dest_string = new_list[i];

    int new_len = remove_digits_from_string(current_src_string, current_string_original_len, current_dest_string);
    new_lengths[i] = new_len;
    total_chars_removed += (current_string_original_len - new_len);
  }

  // Return the total number of characters in the modified list (sum of new lengths)
  return total_chars(list, lengths, num_strings) - total_chars_removed;
}
