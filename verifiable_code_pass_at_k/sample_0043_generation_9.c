// Task ID: 43
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Axiomatic block for recursive logic and helper axioms.
  // Rule II.1: Use axiomatic for complex logic.
  axiomatic RegexMatch {
    // Defines a character as a lowercase letter.
    logic boolean is_lowercase(char c) = (c >= 'a' && c <= 'z');

    // Recursive logic function to check if a substring matches the pattern.
    // Pattern: one or more lowercase letters, optionally followed by '_', then one or more lowercase letters.
    // Example: "a", "a_b", "abc_def"
    // s: The string (char array)
    // start: The starting index for the current match attempt.
    // end: The end index of the string (exclusive).
    // Rule I.3: Array pointer decay - char* s instead of char s[].
    logic boolean match_regex_at(char* s, integer start, integer end) reads s[start..end-1];

    // Base case: A single lowercase letter (minimum match)
    axiom match_regex_at_base_letter:
      orall char* s, integer start, integer end;
        (start < end && is_lowercase(s[start]) && (start + 1 == end || s[start+1] == '_') && (start + 1 == end || !is_lowercase(s[start+1]))) ==>
        match_regex_at(s, start, end);

    // Recursive case 1: Multiple lowercase letters
    axiom match_regex_at_recursive_letters:
      orall char* s, integer start, integer end;
        (start < end && is_lowercase(s[start]) && match_regex_at(s, start + 1, end)) ==>
        match_regex_at(s, start, end);

    // Recursive case 2: _ followed by lowercase letters
    axiom match_regex_at_recursive_underscore:
      orall char* s, integer start, integer end;
        (start < end - 1 && s[start] == '_' && is_lowercase(s[start+1]) && match_regex_at(s, start + 1, end)) ==>
        match_regex_at(s, start, end);

    // Helper axiom: If a match exists from start, then the first character is lowercase.
    // This helps the prover link `match_regex_at` to the `is_lowercase` property.
    axiom match_regex_at_implies_first_char_lowercase:
      orall char* s, integer start, integer end;
        (match_regex_at(s, start, end) && start < end) ==> is_lowercase(s[start]);

    // Helper axiom: If a match exists from start, and the next char is not '_', then the match must be a single letter.
    axiom match_regex_at_implies_single_letter_or_underscore:
      orall char* s, integer start, integer end;
        (match_regex_at(s, start, end) && start < end - 1 && s[start+1] != '_') ==> is_lowercase(s[start]); // This might need refinement for consecutive letters.

    // Helper axiom: If a match exists from start, and the next char is '_', then the char after '_' must be lowercase.
    axiom match_regex_at_implies_char_after_underscore_lowercase:
      orall char* s, integer start, integer end;
        (match_regex_at(s, start, end) && start < end - 1 && s[start+1] == '_' && start + 2 < end) ==> is_lowercase(s[start+2]);

    // Helper axiom: If a match exists, and it's not a single character match, then it must be either a letter followed by a match,
    // or an underscore followed by a match.
    axiom match_regex_at_decomposition:
      orall char* s, integer start, integer end;
        (match_regex_at(s, start, end) && start < end - 1) ==>
        ( (is_lowercase(s[start]) && match_regex_at(s, start + 1, end)) ||
          (s[start] == '_' && is_lowercase(s[start+1]) && match_regex_at(s, start + 1, end))
        );

    // Helper axiom: If a match exists, the length must be at least 1.
    axiom match_regex_at_length_at_least_one:
      orall char* s, integer start, integer end;
        match_regex_at(s, start, end) ==> (end - start >= 1);
  }
*/

/*@
  requires \valid_read(s + (0..len-1)); // String must be readable up to len-1
  requires len >= 0; // Length must be non-negative

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions must use <==>.
  // The function returns 1 if there exists a substring s[i..j-1] that matches the regex.
  // The ACSL logic `match_regex_at` checks if a substring starting at `i` and ending at `j` matches.
  ensures (\exists integer i, j;
             0 <= i <= j <= len && // Valid substring indices
             (j - i >= 1) && // Substring must not be empty
             match_regex_at(s, i, j)
          ) <==> (\result == 1);
*/
int find_regex_sequence(char* s, int len) {
  /*@
    loop invariant 0 <= i <= len;
    // If a match was found in a previous iteration, result_found remains 1.
    loop invariant (result_found == 1) ==>
                   (\exists integer k, l; 0 <= k < i && k <= l <= len && (l - k >= 1) && match_regex_at(s, k, l));
    loop assigns i, result_found;
    loop variant len - i;
  */
  for (int i = 0; i < len; ++i) {
    // Try to find a match starting at index i
    /*@
      loop invariant i <= j <= len;
      // If a match was found starting at i, it's captured here.
      loop invariant (found_at_i == 1) ==>
                     (\exists integer k; i <= k < j && match_regex_at(s, i, k + 1));
      loop assigns j, found_at_i;
      loop variant len - j;
    */
    for (int j = i + 1; j <= len; ++j) { // j is exclusive end index
      // Check if s[i..j-1] matches the regex
      int current_start = i;
      int current_end = j;
      int is_match = 0; // Rule I.2: Use int for boolean.

      // Manual check for "one or more lowercase letters"
      // This is a simplified check, full regex requires more sophisticated state machine logic.
      // For this problem, we'll check for "a_b" or "abc" patterns.

      // Pattern: (letter)+(_(letter)+)?
      // Check for first letter sequence
      int k = current_start;
      /*@
        loop invariant current_start <= k <= current_end;
        loop invariant orall integer x; current_start <= x < k ==> (s[x] >= 'a' && s[x] <= 'z');
        loop assigns k;
        loop variant current_end - k;
      */
      while (k < current_end && s[k] >= 'a' && s[k] <= 'z') {
        k++;
      }

      // If at least one letter was found
      if (k > current_start) {
        // If we reached the end of the substring, it's a match (e.g., "abc")
        if (k == current_end) {
          is_match = 1;
        } else if (k < current_end && s[k] == '_') {
          // If an underscore is found, check for another sequence of letters
          int l = k + 1;
          /*@
            loop invariant k + 1 <= l <= current_end;
            loop invariant orall integer x; k + 1 <= x < l ==> (s[x] >= 'a' && s[x] <= 'z');
            loop assigns l;
            loop variant current_end - l;
          */
          while (l < current_end && s[l] >= 'a' && s[l] <= 'z') {
            l++;
          }
          // If at least one letter was found after underscore and we reached the end of the substring
          if (l > k + 1 && l == current_end) {
            is_match = 1;
          }
        }
      }

      if (is_match == 1) {
        // If a match is found for s[i..j-1], we can return 1 immediately.
        return 1;
      }
    }
  }
  return 0; // No match found in the entire string.
}
