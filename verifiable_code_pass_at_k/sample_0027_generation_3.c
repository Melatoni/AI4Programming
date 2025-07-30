// Task ID: 27
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Recursive logic for complexity.
  // Defines a property for a single character: is it a digit?
  axiomatic CharProperties {
    logic boolean is_digit(char c);

    axiom is_digit_def_0: is_digit('0');
    axiom is_digit_def_1: is_digit('1');
    axiom is_digit_def_2: is_digit('2');
    axiom is_digit_def_3: is_digit('3');
    axiom is_digit_def_4: is_digit('4');
    axiom is_digit_def_5: is_digit('5');
    axiom is_digit_def_6: is_digit('6');
    axiom is_digit_def_7: is_digit('7');
    axiom is_digit_def_8: is_digit('8');
    axiom is_digit_def_9: is_digit('9');

    // Helper axiom: if a char is not one of '0'..'9', it's not a digit.
    axiom is_digit_neg_ge:
      \forall char c; c < '0' || c > '9' ==> !is_digit(c);

    // Defines a property for a string: does it contain any digits?
    logic boolean contains_digit(char* s, int len);

    axiom contains_digit_base:
      \forall char* s, int len; len <= 0 ==> !contains_digit(s, len);

    axiom contains_digit_recursive:
      \forall char* s, int len; len > 0 ==>
        (contains_digit(s, len) <==> (is_digit(s[0]) || contains_digit(s + 1, len - 1)));

    // Helper axiom: if all characters are non-digits, the string contains no digits.
    axiom contains_digit_helper_neg:
      \forall char* s, int len;
        (\forall integer i; 0 <= i < len ==> !is_digit(s[i])) ==> !contains_digit(s, len);

    // Helper axiom: if a string contains a digit, there exists an index where it's a digit.
    axiom contains_digit_helper_pos:
      \forall char* s, int len;
        contains_digit(s, len) ==> (\exists integer i; 0 <= i < len && is_digit(s[i]));
  }
*/

/*@
  // Helper function to check if a character is a digit.
  // Rule II.3: Ensures clause uses logical equivalence.
  assigns \nothing;
  ensures (\result == 1) <==> (c >= '0' && c <= '9');
*/
int is_char_digit(char c) {
    if (c >= '0' && c <= '9') {
        return 1;
    }
    return 0;
}

/*@
  // Helper function to calculate string length.
  // Rule II.5: Requires clause for non-null string.
  requires s != \null;
  assigns \nothing;
  ensures \result >= 0;
  ensures s[\result] == '\0';
  ensures \forall integer k; 0 <= k < \result ==> s[k] != '\0';
*/
int string_length(char* s) {
    int len = 0;
    /*@
      loop invariant len >= 0;
      loop invariant \forall integer k; 0 <= k < len ==> s[k] != '\0';
      loop variant \strlen(s) - len; // Frama-C's built-in strlen
    */
    while (s[len] != '\0') {
        len++;
    }
    return len;
}

/*@
  // Function to remove all digits from a single string.
  // s is the input string (read-only).
  // result is the output string (modified).
  // max_len is the maximum possible length of the result string (which is len of s + 1 for null terminator).

  // Rule II.5: Prevent RTEs.
  requires s != \null;
  requires result != \null;
  requires \valid(s);
  requires \valid(s + (0 .. string_length(s)));
  requires \valid(result + (0 .. max_len - 1));
  requires max_len >= string_length(s) + 1; // Ensure result buffer is large enough

  assigns result[0..max_len-1];

  // Post-conditions for the transformation:
  // 1. The result string is null-terminated.
  ensures result[\result] == '\0';
  // 2. The length of the result string is \result.
  ensures \result >= 0;
  // 3. All characters in the result string are non-digits.
  ensures \forall integer k; 0 <= k < \result ==> !is_digit(result[k]);
  // 4. The result string contains characters from s in their original relative order,
  //    excluding digits.
  ensures \forall integer i, j; 0 <= i < \result && 0 <= j < \result && i < j ==>
    (\exists integer x, y; 0 <= x < string_length(s) && 0 <= y < string_length(s) && x < y &&
     !is_digit(s[x]) && !is_digit(s[y]) && result[i] == s[x] && result[j] == s[y]);
  // 5. Every non-digit character from s appears in result.
  ensures \forall integer k; 0 <= k < string_length(s) ==>
    (!is_digit(s[k]) ==> (\exists integer l; 0 <= l < \result && result[l] == s[k]));
  // 6. The length of the result string is the count of non-digit characters in s.
  ensures \result == (\sum integer k; 0 <= k < string_length(s) && !is_digit(s[k]));
*/
int remove_digits_from_string(char* s, char* result, int max_len) {
    int s_idx = 0;
    int result_idx = 0;
    int s_len = string_length(s);

    /*@
      loop invariant s_idx >= 0 && s_idx <= s_len;
      loop invariant result_idx >= 0 && result_idx <= s_idx;
      loop invariant result_idx <= max_len; // Ensure we don't write out of bounds
      // All characters processed so far in 's' have been correctly handled.
      // Non-digits are copied, digits are skipped.
      loop invariant \forall integer k; 0 <= k < s_idx ==>
        (is_digit(s[k]) ==> (\forall integer l; 0 <= l < result_idx && result[l] != s[k]));
      loop invariant \forall integer k; 0 <= k < result_idx ==> !is_digit(result[k]);
      // The content of result buffer up to result_idx correctly reflects non-digits from s up to s_idx
      loop invariant result_idx == (\sum integer k; 0 <= k < s_idx && !is_digit(s[k]));

      loop assigns s_idx, result_idx, result[0..max_len-1];
      loop variant s_len - s_idx;
    */
    while (s_idx < s_len) {
        /*@
          assert s_idx < s_len && s[s_idx] != '\0';
          assert result_idx < max_len; // Ensure there's space for potential copy + null terminator
        */
        if (!is_char_digit(s[s_idx])) {
            result[result_idx] = s[s_idx];
            result_idx++;
        }
        s_idx++;
    }
    // Rule II.5: Ensure null termination within bounds.
    /*@ assert result_idx < max_len; */
    result[result_idx] = '\0';
    return result_idx;
}

/*@
  // Function to remove digits from a list of strings.
  // inputs: array of pointers to strings.
  // outputs: array of pointers to result buffers.
  // num_strings: number of strings in the input array.
  // max_string_len: maximum possible length of any string in inputs (used for buffer allocation).

  requires inputs != \null;
  requires outputs != \null;
  requires num_strings >= 0;
  requires max_string_len >= 0;

  // Each input string pointer must be valid.
  requires \valid_read(inputs + (0 .. num_strings - 1));
  // Each output buffer pointer must be valid and point to a sufficiently sized buffer.
  requires \valid(outputs + (0 .. num_strings - 1));
  requires \forall integer i; 0 <= i < num_strings ==>
    (\valid(inputs[i] + (0 .. string_length(inputs[i]))) &&
     \valid(outputs[i] + (0 .. max_string_len))); // max_string_len + 1 for null terminator, assuming max_string_len already accounts for it.

  assigns outputs[0..num_strings-1][0..max_string_len];

  // Post-conditions:
  // For each string in the input, its corresponding output string has digits removed.
  ensures \forall integer i; 0 <= i < num_strings ==>
    (\exists integer len;
       outputs[i][len] == '\0' &&
       (\forall integer k; 0 <= k < len ==> !is_digit(outputs[i][k])) &&
       len == (\sum integer k; 0 <= k < string_length(inputs[i]) && !is_digit(inputs[i][k]))
    );
*/
void remove_digits_from_list(char** inputs, char** outputs, int num_strings, int max_string_len) {
    int i = 0;
    /*@
      loop invariant i >= 0 && i <= num_strings;
      // All strings processed so far have had their digits removed correctly.
      loop invariant \forall integer k; 0 <= k < i ==>
        (\exists integer len;
           outputs[k][len] == '\0' &&
           (\forall integer l; 0 <= l < len ==> !is_digit(outputs[k][l])) &&
           len == (\sum integer l; 0 <= l < string_length(inputs[k]) && !is_digit(inputs[k][l]))
        );
      loop assigns i, outputs[0..num_strings-1][0..max_string_len];
      loop variant num_strings - i;
    */
    while (i < num_strings) {
        // Call the helper function for each string.
        // We pass max_string_len + 1 as the buffer size for the null terminator.
        remove_digits_from_string(inputs[i], outputs[i], max_string_len + 1);
        i++;
    }
}
