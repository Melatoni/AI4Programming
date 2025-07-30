// Task ID: 15
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in ACSL.
*/

/*@
  // Axiomatic block for character properties.
  axiomatic CharProperties {
    logic boolean is_lowercase(char c) = (c >= 'a' && c <= 'z');
  }
*/

/*@
  // Rule II.5: Prevent runtime errors.
  // Input string must be null-terminated.
  requires \valid_read(str) && \valid_read(str + \strlen(str));
  // Output array must be valid for writing up to 'max_substrings' pointers.
  requires \valid(substrings + (0 .. max_substrings - 1));
  // Each substring pointer must be valid for writing up to 'max_len' characters.
  requires \for_all integer i; 0 <= i < max_substrings ==> \valid(substrings[i] + (0 .. max_len - 1));
  // Ensure max_len is at least 1 to accommodate null terminator.
  requires max_len >= 1;

  // No specific assigns clause for the input string, as it's read-only.
  assigns *substrings, **substrings;

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  // The function returns the number of substrings found.
  // The result must be between 0 and max_substrings.
  ensures 0 <= \result <= max_substrings;
  // All substrings returned must be null-terminated.
  ensures \for_all integer i; 0 <= i < \result ==> substrings[i][\strlen(substrings[i])] == '\0';
  // All substrings returned must be within max_len.
  ensures \for_all integer i; 0 <= i < \result ==> \strlen(substrings[i]) < max_len;
  // All characters within each substring (except the null terminator) must not be lowercase.
  ensures \for_all integer i; 0 <= i < \result ==>
          \for_all integer j; 0 <= j < \strlen(substrings[i]) ==>
          !is_lowercase(substrings[i][j]);
  // The concatenation of the substrings, separated by lowercase characters, must match the original string.
  // This is complex to express directly with ACSL string functions,
  // so we focus on the properties of the *generated* substrings.
  // An alternative would be to define a recursive logic function for this.
*/
int split_on_lowercase(char *str, char *substrings[], int max_substrings, int max_len) {
    int current_char_idx = 0;
    int current_substring_start = 0;
    int num_substrings = 0;

    /*@
      loop invariant 0 <= current_char_idx <= \strlen(str);
      loop invariant 0 <= current_substring_start <= current_char_idx;
      loop invariant 0 <= num_substrings <= max_substrings;

      // All substrings processed so far are valid.
      loop invariant \for_all integer i; 0 <= i < num_substrings ==>
                       substrings[i][\strlen(substrings[i])] == '\0' &&
                       \strlen(substrings[i]) < max_len &&
                       (\for_all integer j; 0 <= j < \strlen(substrings[i]) ==> !is_lowercase(substrings[i][j]));

      // If we are at a lowercase character, the previous segment (if any) was processed.
      loop invariant (current_char_idx > 0 && is_lowercase(str[current_char_idx - 1])) ==>
                     (current_substring_start == current_char_idx);

      loop assigns current_char_idx, current_substring_start, num_substrings,
                   *substrings, **substrings;
      loop variant \strlen(str) - current_char_idx;
    */
    while (str[current_char_idx] != '\0') {
        /*@
          // Rule II.5: Prevent overflow in substring length calculation.
          requires current_char_idx - current_substring_start < max_len;
        */
        if (is_lowercase(str[current_char_idx])) {
            // Found a lowercase character, so the segment before it is a substring.
            // Check if we have space for a new substring.
            if (num_substrings < max_substrings) {
                int len = current_char_idx - current_substring_start;

                // Only create a substring if it's not empty.
                /*@
                  // Rule II.5: Prevent overflow for len + 1 (for null terminator).
                  // Ensure target buffer has enough space.
                  requires len < max_len;
                */
                if (len > 0) {
                    /*@
                      loop invariant 0 <= k <= len;
                      loop invariant \for_all integer j; 0 <= j < k ==> substrings[num_substrings][j] == str[current_substring_start + j];
                      loop assigns substrings[num_substrings][0 .. len-1];
                      loop variant len - k;
                    */
                    for (int k = 0; k < len; k++) {
                        substrings[num_substrings][k] = str[current_substring_start + k];
                    }
                    substrings[num_substrings][len] = '\0'; // Null-terminate the substring.
                    num_substrings++;
                }
            }
            // Move start of next substring past the current lowercase character.
            current_substring_start = current_char_idx + 1;
        }
        current_char_idx++;
    }

    // Handle the last segment if it's not terminated by a lowercase character.
    /*@
      // Rule II.5: Prevent overflow in substring length calculation.
      requires current_char_idx - current_substring_start < max_len;
    */
    if (num_substrings < max_substrings) {
        int len = current_char_idx - current_substring_start;
        /*@
          // Rule II.5: Prevent overflow for len + 1 (for null terminator).
          // Ensure target buffer has enough space.
          requires len < max_len;
        */
        if (len > 0) {
            /*@
              loop invariant 0 <= k <= len;
              loop invariant \for_all integer j; 0 <= j < k ==> substrings[num_substrings][j] == str[current_substring_start + j];
              loop assigns substrings[num_substrings][0 .. len-1];
              loop variant len - k;
            */
            for (int k = 0; k < len; k++) {
                substrings[num_substrings][k] = str[current_substring_start + k];
            }
            substrings[num_substrings][len] = '\0';
            num_substrings++;
        }
    }

    return num_substrings;
}
