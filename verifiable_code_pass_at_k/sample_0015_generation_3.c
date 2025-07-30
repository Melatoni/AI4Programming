// Task ID: 15
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as string is char*.

  // Rule II.1: Recursive logic for complexity (not directly needed for this problem).
  // Rule II.2: Helper axioms (not directly needed for this problem).
  // Rule II.3: Ensures clause for boolean-like functions must use <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE) - check for null string, valid length.

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.

  // Problem: Split a string at lowercase letters.
  // This function returns 1 if the string contains only uppercase letters or non-alphabetic characters,
  // or if the string is empty.
  // It returns 0 if the string contains at least one lowercase letter.
*/

/*@
  requires \valid_read(s) || s == \null;
  requires \valid_read(s + (0..len-1));
  requires len >= 0;

  assigns \nothing;

  // ACSL helper predicate to check if a character is a lowercase letter.
  // Note: For ASCII, 'a' through 'z' are contiguous.
  predicate is_lowercase(char c) = c >= 'a' && c <= 'z';

  // The function returns 0 if there exists a lowercase letter, 1 otherwise.
  ensures (\exists integer i; 0 <= i < len && is_lowercase(s[i])) <==> (\result == 0);
  ensures (\forall integer i; 0 <= i < len ==> !is_lowercase(s[i])) <==> (\result == 1);
*/
int contains_no_lowercase(char const *s, int len) {
    if (s == (char const *)\null) {
        return 1; // An empty or null string contains no lowercase letters.
    }

    /*@
      loop invariant 0 <= i <= len;
      // Invariant: No lowercase characters found in the prefix s[0..i-1].
      loop invariant \forall integer k; 0 <= k < i ==> !is_lowercase(s[k]);
      loop assigns i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Check if the character is a lowercase letter.
        // Assuming ASCII or compatible character encoding for 'a' through 'z' contiguity.
        if (s[i] >= 'a' && s[i] <= 'z') {
            return 0; // Found a lowercase letter.
        }
    }
    return 1; // No lowercase letters found in the entire string.
}
