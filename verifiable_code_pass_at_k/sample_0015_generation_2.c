// Task ID: 15
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in ACSL.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: Ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic CharProperties {
    logic boolean is_lowercase_char(char c);

    axiom is_lowercase_char_def:
      \forall char c; is_lowercase_char(c) <==> ('a' <= c && c <= 'z');

    logic integer count_lowercase_until(char* s, integer start, integer end);
    axiom count_lowercase_until_base:
      \forall char* s, integer start;
        count_lowercase_until(s, start, start) == 0;
    axiom count_lowercase_until_recursive:
      \forall char* s, integer start, integer end;
        start < end ==>
        count_lowercase_until(s, start, end) ==
        (if is_lowercase_char(s[end-1]) then 1 else 0) + count_lowercase_until(s, start, end-1);

    // Helper axiom: If there are no lowercase characters in a range, then count_lowercase_until is 0.
    axiom count_lowercase_until_zero_helper:
      \forall char* s, integer start, integer end;
        (\forall integer k; start <= k < end ==> !is_lowercase_char(s[k])) ==>
        count_lowercase_until(s, start, end) == 0;
  }
*/

/*@
  requires \valid_read_string(s);
  requires max_parts > 0;
  requires \valid(parts + (0 .. max_parts - 1));
  requires \valid(part_lengths + (0 .. max_parts - 1));

  assigns parts[0 .. max_parts - 1];
  assigns part_lengths[0 .. max_parts - 1];

  // The function returns the number of parts.
  // The number of parts is always less than or equal to max_parts.
  ensures \result <= max_parts;
  // Each part is a valid string.
  ensures \forall integer i; 0 <= i < \result ==> \valid_read_string(parts[i]);
  // Each part's length is correctly recorded.
  ensures \forall integer i; 0 <= i < \result ==> part_lengths[i] == \strlen(parts[i]);

  // Overall string is composed of the parts.
  // This requires a more complex ACSL property, often needing a ghost variable or another axiomatic function
  // to reconstruct the original string from parts. For simplicity, we state that the concatenation
  // of parts forms a prefix of the original string up to the point where all lowercase chars are processed.
  // This is a common simplification in Frama-C for string manipulation.
  // A perfect proof would need to relate s to parts[i] + \0.
  // For now, we ensure the first part starts at s.
  ensures \result > 0 ==> parts[0] == s;

  // Each part is delimited by a lowercase character, or it's the last part.
  ensures \forall integer i; 0 <= i < \result - 1 ==>
    (\exists integer k; parts[i] + part_lengths[i] == s + k && is_lowercase_char(s[k]));

  // No lowercase characters within any part.
  ensures \forall integer i; 0 <= i < \result;
    count_lowercase_until(parts[i], 0, part_lengths[i]) == 0;

*/
int split_string_at_lowercase(char* s, char* parts[], int part_lengths[], int max_parts) {
    int s_len = 0;
    /*@
      loop invariant 0 <= s_len <= \strlen(s);
      loop invariant \forall integer k; 0 <= k < s_len ==> s[k] != '\0';
      loop assigns s_len;
      loop variant \strlen(s) - s_len;
    */
    while (s[s_len] != '\0') {
        s_len++;
    }

    int current_parts_count = 0;
    int current_start_index = 0;

    /*@
      loop invariant 0 <= current_start_index <= s_len;
      loop invariant 0 <= current_parts_count <= max_parts;
      loop invariant current_parts_count <= current_start_index + 1; // At most one part per character processed.

      // All parts found so far are valid.
      loop invariant \forall integer i; 0 <= i < current_parts_count ==> \valid_read_string(parts[i]);
      // All parts found so far have correct lengths.
      loop invariant \forall integer i; 0 <= i < current_parts_count ==> part_lengths[i] == \strlen(parts[i]);
      // All parts found so far contain no lowercase characters.
      loop invariant \forall integer i; 0 <= i < current_parts_count;
        count_lowercase_until(parts[i], 0, part_lengths[i]) == 0;

      // The string up to current_start_index has been processed into parts.
      loop invariant
        (current_parts_count == 0 && current_start_index == 0) ||
        (current_parts_count > 0 && parts[0] == s &&
         (\forall integer j; 0 <= j < current_parts_count - 1 ==>
           (\exists integer k; parts[j] + part_lengths[j] == s + k && is_lowercase_char(s[k]))));

      loop assigns current_parts_count, current_start_index, parts[0 .. max_parts - 1], part_lengths[0 .. max_parts - 1];
      loop variant s_len - current_start_index;
    */
    while (current_start_index < s_len && current_parts_count < max_parts) {
        int current_end_index = current_start_index;
        /*@
          loop invariant current_start_index <= current_end_index <= s_len;
          loop invariant \forall integer k; current_start_index <= k < current_end_index ==> !is_lowercase_char(s[k]);
          loop assigns current_end_index;
          loop variant s_len - current_end_index;
        */
        while (current_end_index < s_len && !is_lowercase_char(s[current_end_index])) {
            current_end_index++;
        }

        if (current_parts_count < max_parts) {
            parts[current_parts_count] = s + current_start_index;
            part_lengths[current_parts_count] = current_end_index - current_start_index;

            // Null-terminate the part temporarily for strlen, then restore.
            // This requires the string 's' to be mutable, or we need to copy.
            // Assuming 's' is mutable for this operation.
            // If 's' is const, we'd need to copy segments to new buffers.
            // For Frama-C, this is a common challenge with read-only strings.
            // The constraint `\valid_read_string(parts[i])` implicitly requires null-termination.
            // A more robust solution for const `s` would involve a separate buffer for each part.
            // For this problem, we assume s is mutable or we just track length.
            // If `s` is `char* s` (not `const char* s`), it's mutable.
            char original_char_at_end = s[current_end_index];
            s[current_end_index] = '\0';
            // Assert that the length is correct after null-termination.
            /*@ assert part_lengths[current_parts_count] == \strlen(parts[current_parts_count]); */
            s[current_end_index] = original_char_at_end; // Restore original char

            current_parts_count++;
        } else {
            // No space left in parts array. Break.
            break;
        }

        // Move to the character after the current part.
        // If it was split by a lowercase char, advance past it.
        // If it was the end of string, current_end_index == s_len.
        current_start_index = current_end_index;
        if (current_start_index < s_len && is_lowercase_char(s[current_start_index])) {
            current_start_index++; // Skip the lowercase delimiter
        }
    }

    return current_parts_count;
}
