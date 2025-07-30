// Task ID: 39
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper axioms.
  axiomatic CharProperties {
    logic integer count_char_in_string(char_ptr s, integer len, char c) reads s;

    axiom count_char_in_string_empty:
      \forall char_ptr s, char c;
        count_char_in_string(s, 0, c) == 0;

    axiom count_char_in_string_recursive:
      \forall char_ptr s, integer len, char c;
        len > 0 ==>
        count_char_in_string(s, len, c) ==
          (if s[len - 1] == c then 1 else 0) + count_char_in_string(s, len - 1, c);

    // Helper axiom: Maximum count of any character in a string.
    logic integer max_char_count(char_ptr s, integer len) reads s;

    axiom max_char_count_empty:
      \forall char_ptr s;
        max_char_count(s, 0) == 0;

    axiom max_char_count_recursive:
      \forall char_ptr s, integer len;
        len > 0 ==>
        max_char_count(s, len) ==
          \max(max_char_count(s, len - 1),
               count_char_in_string(s, len, s[len - 1]));

    // Helper axiom: The sum of counts of all characters is the string length.
    // This is implicitly handled by `max_char_count` which finds the max, not sum.
    // The condition for rearrangement is max_freq <= (len + 1) / 2.
    // No specific helper axiom for sum is needed for this problem.
  }
*/

/*@
  requires \valid_read_string(s); // s is a valid null-terminated string.
  requires len >= 0;
  requires \strlen(s) == len; // Ensure len matches the actual string length.

  // Rule II.5: Prevent Runtime Errors. No direct arithmetic overflows here,
  // but ensure len is not excessively large if it were to be used in sizing.
  // The logic (len + 1) / 2 naturally handles integer division.

  assigns \nothing;

  // Rule II.3: CRITICAL - ensures clause for boolean-like functions uses logical equivalence.
  ensures (\exists char_ptr s_ptr;
             // s_ptr points to a permutation of s
             // This part is hard to express purely in ACSL without a full permutation definition.
             // Instead, we use the known mathematical condition for such rearrangement:
             // The count of the most frequent character must not exceed (length + 1) / 2.
             max_char_count(s, len) <= (len + 1) / 2
          ) <==> (result == 1);
*/
int can_rearrange_adjacent_different(char *s, int len) {
    if (len <= 1) {
        return 1; // A string of length 0 or 1 always satisfies the condition.
    }

    // Step 1: Count character frequencies.
    // We can't use an array for counts directly due to char range and fixed size.
    // Instead, we will rely on the `max_char_count` logic function.

    // Step 2: Find the maximum frequency.
    int max_freq = 0;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant max_freq == max_char_count(s, i);
      loop assigns i, max_freq;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Calculate count for s[i] up to current point.
        int current_char_count = 0;
        /*@
          loop invariant 0 <= j <= len;
          loop invariant current_char_count == count_char_in_string(s, j, s[i]);
          loop assigns j, current_char_count;
          loop variant len - j;
        */
        for (int j = 0; j < len; j++) {
            if (s[j] == s[i]) {
                current_char_count++;
            }
        }
        if (current_char_count > max_freq) {
            max_freq = current_char_count;
        }
    }

    // Step 3: Check the condition.
    // If the count of the most frequent character is greater than (length + 1) / 2,
    // then it's impossible to rearrange. Otherwise, it's possible.
    // Rule III.2: No parentheses around if-then-else in ACSL.
    // Rule III.1: No C-style ternary in ACSL.
    if (max_freq <= (len + 1) / 2) {
        return 1;
    } else {
        return 0;
    }
}
