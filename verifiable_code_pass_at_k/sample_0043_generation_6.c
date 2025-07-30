// Task ID: 43
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define axiomatic for pattern matching.
  // This axiomatic models the concept of a character being a lowercase letter.
  axiomatic LowercaseLetter {
    logic boolean is_lowercase_letter(char c);

    axiom is_lowercase_letter_def:
      \forall char c; is_lowercase_letter(c) <==> ('a' <= c <= 'z');
  }

  // This axiomatic models the concept of a character being an underscore.
  axiomatic Underscore {
    logic boolean is_underscore(char c);

    axiom is_underscore_def:
      \forall char c; is_underscore(c) <==> (c == '_');
  }

  // This axiomatic models a sequence of lowercase letters.
  // It's recursive to handle variable length sequences.
  axiomatic LetterSequence {
    // is_letter_sequence(s, start, end) is true if s[start...end-1] is a sequence of lowercase letters.
    logic boolean is_letter_sequence(char *s, int start, int end);

    // Base case: An empty sequence is a letter sequence.
    axiom is_letter_sequence_empty:
      \forall char *s, int start; is_letter_sequence(s, start, start);

    // Recursive case: If the current char is a letter and the rest is a letter sequence.
    // Note: bounds checking is implicit in ACSL logic, but good practice to ensure in preconditions.
    axiom is_letter_sequence_recursive:
      \forall char *s, int start, int end;
        start < end ==> (is_letter_sequence(s, start, end) <==>
                         (is_lowercase_letter(s[start]) && is_letter_sequence(s, start + 1, end)));
  }

  // Helper axiom for LetterSequence: if a sequence is a letter sequence, then all its characters are letters.
  // This helps the prover relate the sequence property to individual characters.
  axiomatic LetterSequenceProperties {
    axiom letter_sequence_implies_letters:
      \forall char *s, int start, int end, int k;
        is_letter_sequence(s, start, end) && start <= k < end ==> is_lowercase_letter(s[k]);
  }

  // Function to check if a character is a lowercase letter.
  // Rule II.3: Use logical equivalence for boolean-like functions.
  // Rule II.5: No runtime errors.
  requires \valid(c);
  assigns \nothing;
  ensures (is_lowercase_letter(*c)) <==> (\result == 1);
*/
int is_lowercase(char *c) {
    return (*c >= 'a' && *c <= 'z');
}

/*@
  // Function to check if a character is an underscore.
  // Rule II.3: Use logical equivalence for boolean-like functions.
  // Rule II.5: No runtime errors.
  requires \valid(c);
  assigns \nothing;
  ensures (is_underscore(*c)) <==> (\result == 1);
*/
int is_underscore_char(char *c) {
    return (*c == '_');
}

/*@
  // Main function to find sequences of lowercase letters joined with an underscore.
  // The function returns 1 if such a sequence is found, 0 otherwise.
  // A sequence is defined as:
  // (lowercase_letter)+ _ (lowercase_letter)+
  // For simplicity, we assume 's' is null-terminated or 'len' is accurate.
  // We search for the *first* occurrence.

  // Preconditions:
  // Rule II.5: Prevent runtime errors.
  requires \valid_read(s + (0..len-1)); // 's' is a valid array of 'len' characters.
  requires len >= 0; // Length must be non-negative.

  // Postconditions:
  // Rule II.3: Use logical equivalence for boolean-like functions.
  ensures (\exists integer i, j, k;
             0 <= i && i < j && j < k && k <= len &&
             // First letter sequence (at least one letter)
             is_letter_sequence(s, i, j) &&
             // Underscore in between
             is_underscore(s[j]) &&
             // Second letter sequence (at least one letter)
             is_letter_sequence(s, j + 1, k)
          ) <==> (\result == 1);

  assigns \nothing; // The function does not modify the string.
*/
int find_regex_sequence(char *s, int len) {
    /*@
      loop invariant 0 <= i <= len;
      // If a sequence was found before current 'i', then result would be 1.
      loop invariant \forall integer i_prev, j_prev, k_prev;
                       0 <= i_prev && i_prev < j_prev && j_prev < k_prev && k_prev < i ==>
                       !(is_letter_sequence(s, i_prev, j_prev) &&
                         is_underscore(s[j_prev]) &&
                         is_letter_sequence(s, j_prev + 1, k_prev));
      loop assigns i;
      loop variant len - i;
    */
    for (int i = 0; i < len; ++i) {
        // Look for the start of the first letter sequence (at least one letter)
        if (is_lowercase(&s[i])) {
            int j = i + 1;
            /*@
              loop invariant i < j <= len;
              loop invariant is_letter_sequence(s, i, j); // The sequence s[i...j-1] is all letters.
              loop invariant \forall integer m; i <= m < j ==> is_lowercase_letter(s[m]);
              loop assigns j;
              loop variant len - j;
            */
            while (j < len && is_lowercase(&s[j])) {
                j++;
            }

            // Check if we found at least one letter and then an underscore
            // Rule II.5: Check bounds for s[j]
            if (j < len && j > i && is_underscore_char(&s[j])) { // j > i ensures at least one letter before '_'
                int k = j + 1;
                /*@
                  loop invariant j < k <= len;
                  loop invariant is_letter_sequence(s, j + 1, k); // The sequence s[j+1...k-1] is all letters.
                  loop invariant \forall integer m; j+1 <= m < k ==> is_lowercase_letter(s[m]);
                  loop assigns k;
                  loop variant len - k;
                */
                while (k < len && is_lowercase(&s[k])) {
                    k++;
                }

                // Check if we found at least one letter after the underscore
                if (k > j + 1) { // k > j+1 ensures at least one letter after '_'
                    return 1; // Found a match
                }
            }
        }
    }
    return 0; // No match found
}
