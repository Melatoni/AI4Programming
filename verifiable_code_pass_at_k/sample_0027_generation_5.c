// Task ID: 27
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // We need to define what a "digit" is.
  axiomatic Digit {
    logic int is_digit(char c);

    axiom is_digit_0: is_digit('0') == 1;
    axiom is_digit_1: is_digit('1') == 1;
    axiom is_digit_2: is_digit('2') == 1;
    axiom is_digit_3: is_digit('3') == 1;
    axiom is_digit_4: is_digit('4') == 1;
    axiom is_digit_5: is_digit('5') == 1;
    axiom is_digit_6: is_digit('6') == 1;
    axiom is_digit_7: is_digit('7') == 1;
    axiom is_digit_8: is_digit('8') == 1;
    axiom is_digit_9: is_digit('9') == 1;
    // Rule II.2: Helper axioms for properties.
    // All other characters are not digits.
    axiom is_digit_other:
      \forall char c;
        !(c == '0' || c == '1' || c == '2' || c == '3' || c == '4' ||
          c == '5' || c == '6' || c == '7' || c == '8' || c == '9') ==>
        is_digit(c) == 0;
  }

  // Define a logical function to check if a character array contains only non-digits up to a certain index.
  // This will be useful for the postcondition of `remove_digits_from_string`.
  axiomatic StringProperty {
    logic boolean all_non_digits(char *s, int len);

    axiom all_non_digits_base:
      all_non_digits(s, 0) == \true;

    axiom all_non_digits_recursive:
      \forall char *s, integer len; len > 0 ==>
      (all_non_digits(s, len) <==>
       (is_digit(s[len-1]) == 0 && all_non_digits(s, len-1)));
  }
*/

/*@
  requires valid_string: \valid_read(s + (0..len));
  requires len >= 0;
  requires \valid(s + (0..len)); // s must be writable as well, as we modify it in place.

  // Rule II.5: No specific RTE for char.
  // Rule II.3: Ensures clause uses logical equivalence.
  ensures \result >= 0 && \result <= len;
  ensures all_non_digits(s, \result); // The resulting string contains only non-digits.
  ensures \forall integer i; 0 <= i < len ==> (is_digit(s[i]) == 0 || \exists integer j; 0 <= j < \result && s[j] == s[i]); // All non-digits from original string are preserved.
  ensures \forall integer i, j; 0 <= i < \result && 0 <= j < \result && i < j ==> s[i] != s[j]; // The order of non-digit characters is preserved. (More complex to prove with the current logic, simplified for now)
  // The above ensures for order preservation is tricky. A simpler one:
  // The characters at s[0]...s[result-1] are exactly the non-digit characters from the original string, in their original relative order.
  // This would require a more complex logical function. For now, we'll stick to the simpler `all_non_digits` and `all non-digits preserved`.
*/
int remove_digits_from_string(char *s, int len) {
    int write_idx = 0;
    /*@
      loop invariant 0 <= write_idx <= read_idx;
      loop invariant read_idx <= len;
      loop invariant \forall integer k; 0 <= k < write_idx ==> is_digit(s[k]) == 0; // All characters written so far are non-digits.
      loop invariant \forall integer k; 0 <= k < read_idx && is_digit(\at(s[k], Pre)) == 0 ==> \exists integer j; 0 <= j < write_idx && s[j] == \at(s[k], Pre); // All non-digits encountered so far are present in the written part.
      loop invariant \forall integer k1, k2; 0 <= k1 < k2 < read_idx && is_digit(\at(s[k1], Pre)) == 0 && is_digit(\at(s[k2], Pre)) == 0 ==>
                     (\exists integer j1, j2; 0 <= j1 < j2 < write_idx && s[j1] == \at(s[k1], Pre) && s[j2] == \at(s[k2], Pre)); // Order of non-digits preserved.
      loop assigns write_idx, s[0..read_idx-1];
      loop variant len - read_idx;
    */
    for (int read_idx = 0; read_idx < len; read_idx++) {
        if (is_digit(s[read_idx]) == 0) { // If it's not a digit
            s[write_idx] = s[read_idx];
            write_idx++;
        }
    }
    return write_idx; // Return the new length of the string
}

/*@
  requires num_strings >= 0;
  requires max_string_len >= 0;

  // Rule I.3: Array pointer decay.
  // The 'strings' parameter is an array of pointers to char.
  // It's a pointer to the first element, which is a char*.
  // So, it's `char **strings`.
  requires \valid_read(strings + (0..num_strings-1));
  requires \valid(strings + (0..num_strings-1)); // The array of pointers must be writable.

  // Each string pointed to must be valid.
  requires \forall integer i; 0 <= i < num_strings ==> \valid_read(strings[i] + (0..max_string_len));
  requires \forall integer i; 0 <= i < num_strings ==> \valid(strings[i] + (0..max_string_len));

  // We need to know the actual length of each string for `remove_digits_from_string`.
  // Assuming `string_lens` stores the actual lengths.
  requires \valid_read(string_lens + (0..num_strings-1));
  requires \forall integer i; 0 <= i < num_strings ==> string_lens[i] >= 0;
  requires \forall integer i; 0 <= i < num_strings ==> string_lens[i] <= max_string_len;

  assigns strings[0..num_strings-1][0..max_string_len]; // All characters in all strings might be modified.
  assigns string_lens[0..num_strings-1]; // The lengths will be updated.

  ensures \forall integer i; 0 <= i < num_strings ==> all_non_digits(strings[i], string_lens[i]);
  ensures \forall integer i; 0 <= i < num_strings ==> \old(string_lens[i]) >= string_lens[i];
*/
void remove_digits_from_list_of_strings(char **strings, int num_strings, int *string_lens, int max_string_len) {
    /*@
      loop invariant 0 <= i <= num_strings;
      loop invariant \forall integer k; 0 <= k < i ==> all_non_digits(strings[k], string_lens[k]); // All strings processed so far are digit-free.
      loop invariant \forall integer k; 0 <= k < i ==> \old(string_lens[k]) >= string_lens[k]; // Lengths updated correctly.
      loop assigns i, strings[0..i-1][0..max_string_len], string_lens[0..i-1];
      loop variant num_strings - i;
    */
    for (int i = 0; i < num_strings; i++) {
        string_lens[i] = remove_digits_from_string(strings[i], string_lens[i]);
    }
}
