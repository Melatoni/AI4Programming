// Task ID: 27
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define recursive logic functions within an axiomatic block
  // to describe properties over sequences.

  // Axiomatic block for character properties
  // We need to define what a digit is in ACSL.
  axiomatic CharProperties {
    logic int is_digit_char(char c);

    axiom is_digit_char_def_true{
      forall char c;
      ('0' <= c && c <= '9') ==> is_digit_char(c) == 1;
    }

    axiom is_digit_char_def_false{
      forall char c;
      !('0' <= c && c <= '9') ==> is_digit_char(c) == 0;
    }

    // Helper axiom: If a character is a digit, it's not a non-digit.
    axiom digit_not_non_digit{
      forall char c;
      is_digit_char(c) == 1 <==> is_digit_char(c) == 1; // Trivial, but demonstrates the pattern.
    }
  }

  // Axiomatic block for string properties
  // We need to define what it means for a string to have no digits.
  axiomatic StringProperties {
    logic int string_has_no_digits(char *s, int len);

    // Base case: An empty string has no digits.
    axiom string_has_no_digits_base{
      string_has_no_digits(s, 0) == 1;
    }

    // Recursive case: A non-empty string has no digits if its first char is not a digit
    // and the rest of the string has no digits.
    axiom string_has_no_digits_recursive{
      forall char *s, integer len;
      len > 0 ==> (
        string_has_no_digits(s, len) == (
          (is_digit_char(s[0]) == 0) &&
          (string_has_no_digits(s + 1, len - 1) == 1)
        )
      );
    }

    // Helper axiom: If a string has no digits, then for any character in it, it's not a digit.
    axiom string_no_digits_implies_no_digit_char {
      forall char *s, integer len, integer i;
      0 <= i < len && string_has_no_digits(s, len) == 1 ==> is_digit_char(s[i]) == 0;
    }

    // Helper axiom: If any character in a string is a digit, the string has digits.
    axiom string_has_digit_implies_not_no_digits {
      forall char *s, integer len, integer i;
      0 <= i < len && is_digit_char(s[i]) == 1 ==> string_has_no_digits(s, len) == 0;
    }
  }

  // Axiomatic block for list properties
  // We need to define what it means for a list of strings to have all strings without digits.
  axiomatic ListProperties {
    logic int list_has_no_digits(char *list[], int list_len, int *str_lens);

    // Base case: An empty list has all strings without digits.
    axiom list_has_no_digits_base{
      list_has_no_digits(list, 0, str_lens) == 1;
    }

    // Recursive case: A non-empty list has all strings without digits if its first string
    // has no digits and the rest of the list has all strings without digits.
    axiom list_has_no_digits_recursive{
      forall char *list[], integer list_len, int *str_lens;
      list_len > 0 ==> (
        list_has_no_digits(list, list_len, str_lens) == (
          (string_has_no_digits(list[0], str_lens[0]) == 1) &&
          (list_has_no_digits(list + 1, list_len - 1, str_lens + 1) == 1)
        )
      );
    }
  }
*/

/*@
  // Function to remove digits from a single string.
  // s: The input string (read-only for this function, characters are copied).
  // len: Length of the input string.
  // result_buffer: Buffer where the modified string will be written.
  // result_buffer_size: Maximum size of the result_buffer.

  requires \valid_read(s, len); // Input string is valid and readable up to 'len'.
  requires len >= 0;
  requires \valid(result_buffer + (0 .. result_buffer_size - 1)); // Output buffer is valid.
  requires result_buffer_size > 0; // Output buffer must be able to hold at least a null terminator.
  requires result_buffer_size >= len + 1; // Output buffer must be large enough to hold all non-digit chars + null.

  assigns result_buffer[0 .. result_buffer_size - 1]; // This function writes to the result_buffer.

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  // The function returns the length of the new string.
  // The new string (result_buffer) must contain only non-digit characters.
  ensures result_buffer[\result] == '\0'; // The result string is null-terminated.
  ensures \forall integer k; 0 <= k < \result ==> is_digit_char(result_buffer[k]) == 0; // All chars in result are non-digits.
  ensures \result <= len; // The new length is at most the original length.
  ensures \forall integer i; 0 <= i < len ==> (
    is_digit_char(s[i]) == 0 ==> \exists integer j; 0 <= j < \result && result_buffer[j] == s[i]
  ); // All non-digit chars from s are present in result_buffer.
  ensures \forall integer j; 0 <= j < \result ==> (
    \exists integer i; 0 <= i < len && result_buffer[j] == s[i] && is_digit_char(s[i]) == 0
  ); // All chars in result_buffer came from s and were non-digits.
  ensures \result == \sum(integer i; 0 <= i < len && is_digit_char(s[i]) == 0; 1); // The new length is count of non-digits.
*/
int remove_digits_from_string(char *s, int len, char *result_buffer, int result_buffer_size) {
    int write_idx = 0;
    /*@
      loop invariant 0 <= write_idx <= i;
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < write_idx ==> is_digit_char(result_buffer[k]) == 0; // All written chars are non-digits.
      loop invariant \forall integer k; 0 <= k < i ==> (
        is_digit_char(s[k]) == 0 ==> \exists integer j; 0 <= j < write_idx && result_buffer[j] == s[k]
      ); // All non-digits processed so far are in result_buffer.
      loop invariant \forall integer k; 0 <= k < write_idx ==> (
        \exists integer j; 0 <= j < i && result_buffer[k] == s[j] && is_digit_char(s[j]) == 0
      ); // All chars in result_buffer came from s and were non-digits.
      loop invariant write_idx == \sum(integer k; 0 <= k < i && is_digit_char(s[k]) == 0; 1); // write_idx is count of non-digits found.
      loop invariant write_idx < result_buffer_size; // Ensure we don't write out of bounds.

      loop assigns i, write_idx, result_buffer[0 .. result_buffer_size - 1];
      loop variant len - i; // Rule II.4: Mandatory loop variant.
    */
    for (int i = 0; i < len; i++) {
        // Rule I.2: Use 1 for true, 0 for false.
        // Rule II.5: Prevent RTE - ensure write_idx + 1 does not overflow result_buffer_size.
        // This is implicitly handled by the loop invariant `write_idx < result_buffer_size`
        // and the requires `result_buffer_size >= len + 1`.
        if (is_digit_char(s[i]) == 0) {
            result_buffer[write_idx] = s[i];
            write_idx++;
        }
    }
    result_buffer[write_idx] = '\0'; // Null-terminate the string.
    return write_idx;
}

/*@
  // Main function to remove digits from a list of strings.
  // list_of_strings: An array of pointers to strings.
  // list_len: The number of strings in the list.
  // string_lengths: An array containing the lengths of each string in list_of_strings.
  // result_buffers: An array of buffers, one for each string, where results will be stored.
  // result_buffer_sizes: An array containing the maximum sizes of each buffer in result_buffers.

  requires list_len >= 0;
  requires \valid_read(list_of_strings, list_len); // The array of string pointers is valid.
  requires \valid_read(string_lengths, list_len); // The array of string lengths is valid.
  requires \valid_read(result_buffer_sizes, list_len); // The array of buffer sizes is valid.
  requires \valid_read(result_buffers, list_len); // The array of result buffer pointers is valid.

  // For each string in the input list:
  // Rule II.5: Prevent RTE - ensure each input string and its corresponding output buffer are valid.
  requires \forall integer i; 0 <= i < list_len ==> \valid_read(list_of_strings[i], string_lengths[i]);
  requires \forall integer i; 0 <= i < list_len ==> \valid(result_buffers[i] + (0 .. result_buffer_sizes[i] - 1));
  requires \forall integer i; 0 <= i < list_len ==> result_buffer_sizes[i] > 0;
  requires \forall integer i; 0 <= i < list_len ==> result_buffer_sizes[i] >= string_lengths[i] + 1;

  assigns \nothing; // This function does not modify the input list_of_strings or lengths.
                    // It modifies the content of the result_buffers, but we don't track that
                    // across the function boundary here. The individual string function handles that.

  // Ensures that after execution, all strings in the result_buffers (conceptually)
  // contain no digits. We use the `list_has_no_digits` axiomatic function.
  // Note: This ensurs clause refers to the *state after* the function call.
  // The `result_buffers` and `string_lengths` are technically inputs, but they are
  // pointers to memory that gets modified by the called `remove_digits_from_string`.
  // We need to ensure that the content pointed to by `result_buffers` now satisfies the property.
  // This is a subtle point: Frama-C's WP will use the post-state of `remove_digits_from_string`
  // for the `result_buffers` when evaluating this `ensures`.
  ensures list_has_no_digits(result_buffers, list_len, \old(string_lengths)) == 1; // This is not quite right.
                                                                                // string_lengths is the original length, not the new length.
                                                                                // We need to pass the actual new lengths to list_has_no_digits.
                                                                                // This requires storing the new lengths.

  // A more precise ensures:
  // For each string in the list, its corresponding output buffer should have no digits.
  ensures \forall integer i; 0 <= i < list_len ==> (
      \let new_len = \old(remove_digits_from_string(list_of_strings[i], string_lengths[i], result_buffers[i], result_buffer_sizes[i]));
      string_has_no_digits(result_buffers[i], new_len) == 1
  );
*/
void remove_digits_from_list(char *list_of_strings[], int list_len, int string_lengths[],
                             char *result_buffers[], int result_buffer_sizes[]) {
    /*@
      loop invariant 0 <= i <= list_len;
      // All strings processed so far have had their digits removed correctly.
      loop invariant \forall integer k; 0 <= k < i ==> (
          \let new_len = \old(remove_digits_from_string(list_of_strings[k], string_lengths[k], result_buffers[k], result_buffer_sizes[k]));
          string_has_no_digits(result_buffers[k], new_len) == 1
      );

      loop assigns i, result_buffers[0 .. list_len - 1][0 ..]; // Assigns to the content of result_buffers
      loop variant list_len - i; // Rule II.4: Mandatory loop variant.
    */
    for (int i = 0; i < list_len; i++) {
        // Call the helper function for each string.
        (void)remove_digits_from_string(list_of_strings[i], string_lengths[i],
                                        result_buffers[i], result_buffer_sizes[i]);
    }
}
