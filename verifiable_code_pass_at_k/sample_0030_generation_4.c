// Task ID: 30
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Helper axiomatic block for string properties.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for properties.
*/
/*@
  axiomatic StringProperties {
    logic integer string_length(char *s);

    axiom string_length_null:
      \forall char *s; s == \null ==> string_length(s) == 0;

    axiom string_length_non_null:
      \forall char *s; s != \null ==> string_length(s) == \strlen(s);

    // Recursive logic to count substrings starting and ending with the same character
    // within a given range [start_idx, end_idx].
    logic integer count_same_char_substrings_in_range(char *s, integer len, integer start_idx, integer end_idx);

    // Base case: If the range is empty or invalid, count is 0.
    axiom count_same_char_substrings_in_range_base:
      \forall char *s, integer len, integer start_idx, integer end_idx;
        start_idx > end_idx || start_idx >= len || end_idx < 0 || start_idx < 0 || end_idx >= len ==>
        count_same_char_substrings_in_range(s, len, start_idx, end_idx) == 0;

    // Recursive step:
    // count_same_char_substrings_in_range(s, len, start_idx, end_idx)
    // = count for s[start_idx..end_idx]
    // = count for s[start_idx..end_idx-1] (substrings ending before end_idx)
    // + count for s[start_idx..end_idx] that end at end_idx
    //   (i.e., s[j..end_idx] where s[j] == s[end_idx] for start_idx <= j <= end_idx)
    axiom count_same_char_substrings_in_range_recursive:
      \forall char *s, integer len, integer start_idx, integer end_idx;
        start_idx <= end_idx && start_idx >= 0 && end_idx < len ==>
        count_same_char_substrings_in_range(s, len, start_idx, end_idx) ==
        (count_same_char_substrings_in_range(s, len, start_idx, end_idx - 1) +
         (\sum integer j; start_idx <= j <= end_idx && s[j] == s[end_idx]; 1));

    // Helper axiom: If start_idx == end_idx, there's exactly 1 substring (the character itself).
    axiom count_same_char_substrings_in_range_single_char:
      \forall char *s, integer len, integer idx;
        idx >= 0 && idx < len ==>
        count_same_char_substrings_in_range(s, len, idx, idx) == 1;

    // Helper axiom: The total count is for the range [0, len-1].
    logic integer count_same_char_substrings(char *s, integer len);

    axiom count_same_char_substrings_def:
      \forall char *s, integer len;
        len >= 0 ==>
        count_same_char_substrings(s, len) == count_same_char_substrings_in_range(s, len, 0, len - 1);
  }
*/

/*@
  requires \valid_read(s);
  requires string_length(s) >= 0; // Length can be 0 for empty string.
  // Rule II.5: Prevent potential overflow for the result.
  // The maximum number of substrings for a string of length N is N*(N+1)/2.
  // For N=65535 (max for char* in some systems), N*(N+1)/2 is approx 2^30.
  // For 'int' max, N approx 65535.
  // We constrain the length to prevent overflow of the 'int' return type.
  // If string_length(s) is L, max substrings is L*(L+1)/2.
  // If L = 65535, result can be ~2*10^9, which fits in signed int.
  // So, let's just make sure string_length(s) is within reasonable bounds for computation.
  // A string length of 30000 would result in 30000 * 30001 / 2 = 450,015,000, which fits in int.
  // A string length of 65535 would result in 65535 * 65536 / 2 = 2,147,450,880, which fits in int.
  // We need to ensure that intermediate count doesn't overflow.
  // Max length that guarantees sum fits in int is 65535.
  requires string_length(s) <= 65535;

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions not applicable here,
  // as it returns a count, not a boolean.
  // The ensures clause describes the post-condition related to the axiomatic definition.
  ensures \result == count_same_char_substrings(s, string_length(s));
*/
int count_substrings_same_char_ends(char *s) {
    int len = string_length(s);
    int count = 0;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant count == count_same_char_substrings_in_range(s, len, 0, i - 1);
      loop assigns i, count;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        /*@
          loop invariant 0 <= j <= i;
          loop invariant count == (\at(count, LoopEntry) +
                                    (\sum integer k; 0 <= k < j && s[k] == s[i]; 1));
          loop assigns j, count;
          loop variant i - j;
        */
        for (int j = 0; j <= i; j++) {
            if (s[i] == s[j]) {
                // Rule II.5: Prevent overflow of count.
                // Loop invariant `count <= (i+1)*(i+2)/2` could be maintained.
                // `i` up to `len-1`. Max `count` is `len*(len+1)/2`.
                // Our `requires` clause `string_length(s) <= 65535` ensures `count` fits `int`.
                count++;
            }
        }
    }
    return count;
}
