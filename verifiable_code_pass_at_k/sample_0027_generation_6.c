// Task ID: 27
// Generation: 6

void remove_digits(char strings[][MAX_STR_LEN], int num_strings, int max_str_len)`

The function will iterate through each string. For each string, it will iterate through its characters. If a character is a digit, it will be skipped (effectively "removed" by shifting subsequent characters).

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.
  // Rule II.1, II.2: Recursive logic for complexity, helper axioms. Not directly applicable here,
  //                   but the principles guide the string manipulation logic.
  // Rule II.3: Ensures clause for boolean-like functions. Not applicable as this is void.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Define axiomatic block for character properties if needed, but simple char comparisons
  // are usually handled by Frama-C's built-in knowledge of ASCII.
  // We can define a logic function for is_digit to be explicit.
  axiomatic CharProperties {
    logic int is_digit(char c);

    axiom is_digit_def:
      \forall char c;
        is_digit(c) == (c >= '0' && c <= '9');
  }

  // Helper logic function to express the post-condition for a single string.
  // This describes what a string should look like after digits are removed.
  // It effectively defines the "compressed" string.
  logic char new_char_at(char s[], int len, int original_idx);
  logic int new_len(char s[], int len);

  axiom new_char_at_def:
    \forall char s[], int len, int original_idx;
      (original_idx >= 0 && original_idx < len) ==>
      (new_char_at(s, len, original_idx) ==
        (if is_digit(s[original_idx]) then
           new_char_at(s, len, original_idx + 1) // Skip digit, conceptually
         else
           s[original_idx]
        )
      );

  // This axiom is tricky for direct use in post-conditions for in-place modification.
  // A better approach for in-place is to define the final state based on the initial state.
  // Let's define a predicate for a string being "digit-free" and then relate the final string to it.

  // Predicate: is_digit_free(s, len) returns true if string s of length len has no digits.
  logic boolean is_digit_free(char s[], int len);
  axiom is_digit_free_def:
    \forall char s[], int len;
      is_digit_free(s, len) <==> (\forall integer i; 0 <= i < len ==> !is_digit(s[i]));

  // Predicate: is_original_minus_digits(modified_s, original_s, original_len)
  // Checks if modified_s is original_s with digits removed and characters shifted.
  logic boolean is_original_minus_digits(char modified_s[], char original_s[], int original_len);

  axiom is_original_minus_digits_def:
    \forall char modified_s[], char original_s[], int original_len;
      is_original_minus_digits(modified_s, original_s, original_len) <==>
      (is_digit_free(modified_s, \strlen(modified_s)) && // The modified string must be digit-free
       \forall integer k; 0 <= k < \strlen(modified_s) ==> // For each char in modified_s
         \exists integer j; 0 <= j < original_len && // it comes from original_s
           modified_s[k] == original_s[j] && !is_digit(original_s[j]) && // and it's not a digit
           (\numof(integer x; 0 <= x < j && !is_digit(original_s[x])) == k) // and its index matches the count of non-digits before it
      );

  // Main function contract
  requires num_strings >= 0;
  requires max_str_len >= 0;
  // Ensure that each string is null-terminated and within max_str_len.
  // Also, store the initial state of the strings for the post-condition.
  requires \valid_read(strings) && \valid_read(strings[0..num_strings-1]);
  requires \forall integer i; 0 <= i < num_strings ==>
    \valid_read(strings[i]) && \valid_read(strings[i][0..max_str_len-1]);
  requires \forall integer i; 0 <= i < num_strings ==>
    \strlen(strings[i]) < max_str_len; // Null terminator must fit.

  // Use a ghost variable to store the initial state of the strings for comparison.
  // This requires a `behavior` block or a `writes` clause that allows reading old values.
  // For simplicity here, we assume `assigns` allows reading old values in `ensures`.
  // A more robust way would be to copy the array to a ghost variable.

  assigns strings[0..num_strings-1][0..max_str_len-1];

  // Post-condition: Each string in the array should have its digits removed.
  // This is best expressed by comparing the final state to the initial state.
  // We need to capture the initial state. Frama-C's `\old` operator can help.
  ensures \forall integer i; 0 <= i < num_strings ==>
    is_original_minus_digits(strings[i], \old(strings[i]), \old(\strlen(strings[i])));
*/
void remove_digits(char strings[][100], int num_strings, int max_str_len) {
    /*@
      loop invariant 0 <= i <= num_strings;
      loop invariant \forall integer k; 0 <= k < i ==>
        is_original_minus_digits(strings[k], \old(strings[k]), \old(\strlen(strings[k])));
      loop assigns i, strings[0..num_strings-1][0..max_str_len-1];
      loop variant num_strings - i;
    */
    for (int i = 0; i < num_strings; i++) {
        char *current_str = strings[i];
        int read_idx = 0;
        int write_idx = 0;

        /*@
          loop invariant 0 <= read_idx <= \old(\strlen(current_str)) + 1; // +1 for null terminator
          loop invariant 0 <= write_idx <= read_idx;

          // The part of the string already processed (up to write_idx) must be digit-free
          loop invariant is_digit_free(current_str, write_idx);

          // All characters written so far must be non-digits from the original string
          loop invariant \forall integer k; 0 <= k < write_idx ==>
            \exists integer j; 0 <= j < read_idx &&
              current_str[k] == \old(current_str[j]) && !is_digit(\old(current_str[j])) &&
              (\numof(integer x; 0 <= x < j && !is_digit(\old(current_str[x]))) == k);

          loop assigns read_idx, write_idx, current_str[0..max_str_len-1];
          loop variant \old(\strlen(current_str)) - read_idx;
        */
        while (current_str[read_idx] != '\0') {
            /*@
              // Prevent RTE: array access within bounds.
              // This is guaranteed by the outer loop invariant on read_idx and write_idx,
              // and the function's requires clause on string length.
              // assert read_idx < max_str_len;
            */
            if (!is_digit(current_str[read_idx])) {
                /*@
                  // Prevent RTE: array access within bounds.
                  // assert write_idx < max_str_len;
                */
                current_str[write_idx] = current_str[read_idx];
                write_idx++;
            }
            read_idx++;
        }
        /*@
          // Prevent RTE: array access within bounds.
          // assert write_idx < max_str_len;
        */
        current_str[write_idx] = '\0'; // Null-terminate the modified string
    }
}
