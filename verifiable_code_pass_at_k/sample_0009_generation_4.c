// Task ID: 9
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic StringLength {
  logic integer string_length(char *s);

  axiom string_length_def:
    \forall char *s; s[string_length(s)] == '\0' && (string_length(s) == 0 || s[string_length(s)-1] != '\0');
  
  // Helper axiom: Length is non-negative
  axiom string_length_non_negative:
    \forall char *s; string_length(s) >= 0;
} */

/*@ axiomatic StringRotation {
  logic char rotated_char(char *s, integer len, integer rotation, integer index);

  axiom rotated_char_def:
    \forall char *s, integer len, integer rotation, integer index;
      (0 <= index < len && 0 <= rotation < len) ==>
      rotated_char(s, len, rotation, index) == s[(index + rotation) % len];

  logic boolean is_same_string(char *s1, char *s2, integer len);

  axiom is_same_string_def:
    \forall char *s1, char *s2, integer len;
      is_same_string(s1, s2, len) <==> (\forall integer i; 0 <= i < len ==> s1[i] == s2[i]);

  logic boolean is_rotated_equal(char *s, integer len, integer rotation);

  axiom is_rotated_equal_def:
    \forall char *s, integer len, integer rotation;
      (0 <= len && 0 <= rotation < len) ==>
      (is_rotated_equal(s, len, rotation) <==>
       (\forall integer i; 0 <= i < len ==> s[i] == rotated_char(s, len, rotation, i)));
} */

/*@
  requires \valid(s + (0..string_length(s)));
  requires string_length(s) > 0; // String must not be empty.
  assigns \nothing;
  
  ensures \result >= 0;
  ensures \result < string_length(s);
  ensures is_rotated_equal(s, string_length(s), \result);
  ensures \forall integer k; 0 <= k < \result ==> !is_rotated_equal(s, string_length(s), k);
*/
int min_rotations_for_same_string(char *s) {
    int n = string_length(s);
    if (n == 0) {
        return 0; // Empty string requires 0 rotations.
    }

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> !is_rotated_equal(s, n, k);
      loop assigns i;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          // Helper assertion to help WP connect rotated_char definition with the loop logic
          assert \forall integer idx; 0 <= idx < n ==> s[idx] == s[(idx + i) % n] <==> is_rotated_equal(s, n, i);
        */
        
        // Check if the string s, rotated by 'i', is equal to the original string s.
        int equal = 1; // Assume equal
        /*@
          loop invariant 0 <= j <= n;
          loop invariant equal == ((\forall integer k; 0 <= k < j ==> s[k] == s[(k + i) % n]));
          loop assigns j, equal;
          loop variant n - j;
        */
        for (int j = 0; j < n; j++) {
            if (s[j] != s[(j + i) % n]) {
                equal = 0; // Not equal
                break;
            }
        }

        if (equal == 1) { // If it's equal, this is the minimum rotation.
            return i;
        }
    }
    
    // This part should technically be unreachable if n > 0, as 0 rotations always yield the same string.
    // However, for formal verification, it's good to have a return statement.
    // The post-condition `ensures \result < string_length(s);` covers this.
    return 0; 
}
