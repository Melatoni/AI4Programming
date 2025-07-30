// Task ID: 16
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans (1 for true, 0 for false).
*/

/*@
  axiomatic String {
    // Rule II.1: Recursive logic for complex properties.
    // Length of a string, assuming null-termination.
    logic integer strlen_logic(char *s) reads s;
    axiom strlen_logic_empty: strlen_logic("") == 0;
    axiom strlen_logic_rec:
      \forall char c, char *s;
      strlen_logic(c + s) == 1 + strlen_logic(s);

    // Checks if a character is a lowercase letter ('a' through 'z').
    logic boolean is_lowercase_letter(char c) = (c >= 'a' && c <= 'z');

    // Checks if a character is an underscore.
    logic boolean is_underscore(char c) = (c == '_');

    // Checks if a substring from start to end (inclusive) consists only of lowercase letters.
    logic boolean is_lowercase_sequence(char *s, integer start, integer end) reads s;
    axiom is_lowercase_sequence_base:
      \forall char *s, integer i;
      is_lowercase_sequence(s, i, i) <==> is_lowercase_letter(s[i]);
    axiom is_lowercase_sequence_rec:
      \forall char *s, integer start, integer end;
      start < end ==> (is_lowercase_sequence(s, start, end) <==> (is_lowercase_letter(s[start]) && is_lowercase_sequence(s, start + 1, end)));

    // Helper axiom: if a sequence is lowercase, then all characters within it are lowercase.
    // Rule II.2: CRITICAL - Helper Axioms.
    axiom is_lowercase_sequence_helper:
      \forall char *s, integer start, integer end, integer k;
      is_lowercase_sequence(s, start, end) && start <= k <= end ==> is_lowercase_letter(s[k]);

    // Checks if a string contains a sequence of lowercase letters joined with an underscore.
    // This is the core logic function for the problem.
    logic boolean contains_valid_sequence(char *s) reads s;
    axiom contains_valid_sequence_def:
      \forall char *s;
      contains_valid_sequence(s) <==>
      (\exists integer i, j, k;
        0 <= i && i <= j && j < k && k < strlen_logic(s) && // Valid indices
        is_lowercase_sequence(s, i, j) &&                   // First lowercase sequence
        is_underscore(s[j+1]) &&                            // Followed by an underscore
        is_lowercase_sequence(s, j + 2, k)                  // Followed by another lowercase sequence
      );
  }
*/

/*@
  requires \valid_read(s);
  requires \valid_read_string(s); // s is a null-terminated string.
  assigns \nothing;
  // Rule II.3: Ensures clause uses logical equivalence.
  ensures contains_valid_sequence(s) <==> (\result == 1);
*/
int find_sequence(char *s) {
    /*@
      loop invariant 0 <= i <= strlen_logic(s);
      loop invariant \forall integer k; 0 <= k < i ==> !(\exists integer j, l; k <= j && j < l && l < strlen_logic(s) && is_lowercase_sequence(s, k, j) && is_underscore(s[j+1]) && is_lowercase_sequence(s, j+2, l));
      loop assigns i;
      loop variant strlen_logic(s) - i;
    */
    for (int i = 0; s[i] != '\0'; i++) {
        // Find the start of the first lowercase sequence
        if (!is_lowercase_letter(s[i])) {
            continue;
        }

        // Rule II.4: Mandatory loop annotations.
        /*@
          loop invariant i <= j <= strlen_logic(s);
          loop invariant is_lowercase_sequence(s, i, j-1);
          loop assigns j;
          loop variant strlen_logic(s) - j;
        */
        int j = i;
        while (s[j] != '\0' && is_lowercase_letter(s[j])) {
            j++;
        }

        // At this point, s[i..j-1] is the first lowercase sequence.
        // Check if it's followed by an underscore.
        // Rule II.5: Prevent RTE. Ensure j+1 is a valid index.
        if (s[j] == '\0' || !is_underscore(s[j])) {
            i = j; // Continue search from after the current sequence/non-letter
            continue;
        }

        // Check if the underscore is followed by another lowercase sequence.
        // Rule II.5: Prevent RTE. Ensure j+1 is a valid index for s[j+1].
        if (s[j+1] == '\0' || !is_lowercase_letter(s[j+1])) {
            i = j; // Continue search from after the current sequence/non-letter
            continue;
        }

        // Rule II.4: Mandatory loop annotations.
        /*@
          loop invariant j + 1 <= k <= strlen_logic(s);
          loop invariant is_lowercase_sequence(s, j + 1, k - 1);
          loop assigns k;
          loop variant strlen_logic(s) - k;
        */
        int k = j + 1;
        while (s[k] != '\0' && is_lowercase_letter(s[k])) {
            k++;
        }

        // We found a pattern: s[i..j-1] _ s[j+1..k-1]
        // This means contains_valid_sequence(s) is true.
        return 1;
    }

    // No such sequence found.
    return 0;
}
