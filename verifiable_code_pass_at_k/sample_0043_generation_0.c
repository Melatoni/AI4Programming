// Task ID: 43
// Generation: 0

/*@
  // Rule I.1: No standard library includes are allowed.
  // Rule I.2: Use 'int' for boolean representation (1 for true, 0 for false).
  // Rule II.5: Add requires clauses to prevent runtime errors.
  // Max int value for char codes (ASCII): 127
  // Max length to prevent potential overflow in size-related calculations if any were present.
  // For this problem, max_len is primarily for array bounds.
  requires max_len >= 0;
  requires \valid_read(s + (0 .. max_len - 1));
*/
/*@ axiomatic LowercaseLetter {
  // Rule II.1: Define recursive logic for complex properties.
  // This axiomatic block defines what a lowercase letter is.
  logic int is_lowercase_letter(char c);

  axiom is_lowercase_letter_def:
    \forall char c; is_lowercase_letter(c) == (c >= 'a' && c <= 'z');
}
*/

/*@ axiomatic SequenceWithUnderscore {
  // Rule II.1: Recursive logic to check for a sequence of lowercase letters.
  // This logic function checks if a substring s[start..end-1] consists only of lowercase letters.
  logic int is_lowercase_sequence(char *s, int start, int end);

  axiom is_lowercase_sequence_base:
    \forall char *s, integer start;
      is_lowercase_sequence(s, start, start) == 1; // An empty sequence is considered true

  axiom is_lowercase_sequence_recursive:
    \forall char *s, integer start, integer end;
      start < end ==> (is_lowercase_sequence(s, start, end) ==
                       (is_lowercase_letter(s[end-1]) && is_lowercase_sequence(s, start, end-1)));

  // Rule II.2: Helper axioms are critical for the prover.
  // This helper axiom ensures that if a sequence is lowercase, it remains lowercase for any sub-sequence.
  axiom is_lowercase_sequence_helper_subsequence:
    \forall char *s, integer start, integer end, integer i, integer j;
      is_lowercase_sequence(s, start, end) == 1 && start <= i && i <= j && j <= end ==>
        is_lowercase_sequence(s, i, j) == 1;
}
*/

/*@
  requires \valid_read(s + (0 .. max_len - 1));
  requires max_len >= 0;
  requires index >= 0 && index < max_len;

  // Rule II.3: Use logical equivalence for boolean-like functions.
  ensures \result == 1 <==>
          (index + 1 < max_len && s[index + 1] == '_' &&
           \exists integer k; // Length of the first sequence
             index - k >= 0 && k >= 1 && is_lowercase_sequence(s, index - k, index + 1) == 1 &&
           \exists integer l; // Length of the second sequence
             index + 1 + l < max_len && l >= 1 && is_lowercase_sequence(s, index + 2, index + 2 + l) == 1 &&
           // Ensure the character at 'index' itself is a lowercase letter
           is_lowercase_letter(s[index]) == 1);
*/
int is_sequence_with_underscore_at_index(char *s, int max_len, int index) {
    // Check if the current character is a lowercase letter
    if (!is_lowercase_letter(s[index])) { // Rule I.2: Use int for bool, but the logic function returns int.
        return 0; // Not a lowercase letter
    }

    // Check if the next character is an underscore
    if (index + 1 >= max_len || s[index + 1] != '_') {
        return 0; // No underscore or out of bounds
    }

    // Check for lowercase sequence before the underscore
    /*@
      loop invariant 0 <= i && i <= index;
      loop invariant \forall integer k; i <= k <= index ==> is_lowercase_letter(s[k]) == 1;
      loop assigns i;
      loop variant i;
    */
    int i = index;
    while (i >= 0 && is_lowercase_letter(s[i])) {
        i--;
    }
    // i is now the index of the first character *before* the start of the first sequence, or -1.
    // The first sequence starts at i+1 and ends at index.
    if (i + 1 > index) { // Meaning no lowercase letters before 'index'
        return 0;
    }

    // Check for lowercase sequence after the underscore
    /*@
      loop invariant index + 2 <= j && j <= max_len;
      loop invariant \forall integer k; index + 2 <= k < j ==> is_lowercase_letter(s[k]) == 1;
      loop assigns j;
      loop variant max_len - j;
    */
    int j = index + 2; // Start after the underscore
    while (j < max_len && is_lowercase_letter(s[j])) {
        j++;
    }
    // j is now the index of the first character *after* the end of the second sequence, or max_len.
    // The second sequence starts at index+2 and ends at j-1.
    if (index + 2 >= j) { // Meaning no lowercase letters after '_'
        return 0;
    }

    // If all checks pass, it's a match
    return 1;
}
