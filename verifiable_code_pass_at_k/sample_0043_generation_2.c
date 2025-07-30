// Task ID: 43
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as it's a char array.
  // Rule II.1: Recursive logic for complexity - not applicable here.
  // Rule II.2: Helper axioms - not applicable here.
*/

/*@
  // Axiomatic block for character properties
  axiomatic CharProperties {
    // Rule II.1: Define logic functions for character properties
    logic boolean is_lowercase_letter(char c) = (c >= 'a' && c <= 'z');
    logic boolean is_underscore(char c) = (c == '_');
  }
*/

/*@
  requires \valid_read_string(s);
  requires \strlen(s) >= 0; // String length can be 0.
  // Rule II.5: Prevent runtime errors. Max string length depends on int range.
  // Assuming a reasonable max length for practical purposes, e.g., 2GB,
  // but for Frama-C, it's more about preventing index out of bounds.
  // The string length is implicitly limited by the size of 'int' for the loop counter.

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like return.
  // The function returns 1 if such a sequence exists, 0 otherwise.
  ensures (\exists integer i, j;
            0 <= i && i <= j && j < \strlen(s) && // Valid indices
            (i == 0 || s[i-1] != '_') && // Sequence must not be preceded by '_'
            (j == \strlen(s) - 1 || s[j+1] != '_') && // Sequence must not be followed by '_'
            is_lowercase_letter(s[i]) && // Start with a letter
            is_lowercase_letter(s[j]) && // End with a letter
            (\forall integer k; i <= k <= j && k < \strlen(s) ==> // All characters in range
              (is_lowercase_letter(s[k]) || is_underscore(s[k]))) &&
            (\exists integer k; i < k < j && k < \strlen(s) && is_underscore(s[k]))
          ) <==> (\result == 1);
  assigns \nothing;
*/
int find_regex_sequence(char s[]) {
    int len = 0;
    /*@
      loop invariant 0 <= len <= \strlen(s);
      loop invariant \forall integer k; 0 <= k < len ==> \valid_read(&s[k]);
      loop assigns len;
      loop variant \strlen(s) - len;
    */
    while (s[len] != '\0') {
        len++;
    }

    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i ==>
        !(\exists integer j_inner;
            k <= j_inner && j_inner < len && // Valid indices
            (k == 0 || s[k-1] != '_') && // Sequence must not be preceded by '_'
            (j_inner == len - 1 || s[j_inner+1] != '_') && // Sequence must not be followed by '_'
            is_lowercase_letter(s[k]) && // Start with a letter
            is_lowercase_letter(s[j_inner]) && // End with a letter
            (\forall integer l; k <= l <= j_inner && l < len ==> // All characters in range
              (is_lowercase_letter(s[l]) || is_underscore(s[l]))) &&
            (\exists integer l; k < l < j_inner && l < len && is_underscore(s[l]))
          );
      loop assigns i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Check if s[i] is a lowercase letter and could be the start of a sequence
        if (is_lowercase_letter(s[i])) {
            // Check if it's not preceded by an underscore (or is at the beginning of the string)
            if (i == 0 || s[i-1] != '_') {
                int has_underscore = 0;
                /*@
                  loop invariant i <= j <= len;
                  loop invariant \forall integer k; i <= k < j ==>
                    (is_lowercase_letter(s[k]) || is_underscore(s[k]));
                  loop invariant (has_underscore == 1) <==> (\exists integer k_inner; i < k_inner < j && is_underscore(s[k_inner]));
                  loop assigns j, has_underscore;
                  loop variant len - j;
                */
                for (int j = i; j < len; j++) {
                    if (is_lowercase_letter(s[j])) {
                        // If it's a letter, continue the sequence
                        // If we've found an underscore and this is a letter, and it's not followed by an underscore,
                        // then we found a match.
                        if (has_underscore == 1) {
                            if (j == len - 1 || s[j+1] != '_') {
                                return 1; // Sequence found
                            }
                        }
                    } else if (is_underscore(s[j])) {
                        // If it's an underscore, mark that we've seen one
                        has_underscore = 1;
                    } else {
                        // If it's neither a letter nor an underscore, this sequence is invalid.
                        // Break the inner loop and continue with the next starting index `i`.
                        break;
                    }
                }
            }
        }
    }

    return 0; // No such sequence found
}
