// Task ID: 9
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic StringRotation {
    logic int char_at(char *s, int len, int index);
    axiom char_at_def:
      \forall char *s, integer len, integer index;
        0 <= index < len ==> char_at(s, len, index) == s[index];

    // Helper logic to get a character from a rotated string
    logic int rotated_char_at(char *s, int len, int rotation_amount, int index);
    axiom rotated_char_char_at_def:
      \forall char *s, integer len, integer rotation_amount, integer index;
        0 <= index < len && 0 <= rotation_amount < len ==>
        rotated_char_at(s, len, rotation_amount, index) == char_at(s, len, (index + rotation_amount) % len);

    // Predicate to check if a string is equal to a rotated version of itself
    logic boolean is_rotated_equal(char *s, int len, int rotation_amount);
    axiom is_rotated_equal_def:
      \forall char *s, integer len, integer rotation_amount;
        0 <= len && 0 <= rotation_amount < len ==>
        (is_rotated_equal(s, len, rotation_amount) <==>
         (\forall integer i; 0 <= i < len ==> char_at(s, len, i) == rotated_char_at(s, len, rotation_amount, i)));
  }
*/

/*@
  requires \valid_read_string(s);
  requires len > 0;
  // Rule II.5: Prevent RTE - string length must be positive.
  // Rule II.5: Prevent RTE - rotation amount must be within bounds (handled by logic).

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence.
  // The result is the minimum positive rotation amount `k` such that `s` rotated by `k`
  // is equal to `s`. If no such positive `k` exists (e.g., all characters are the same),
  // then the result is 1 (as per problem description implying at least 1 rotation).
  // For a string like "aaaa", the first rotation (1) gives "aaaa", so result is 1.
  // For "ababa", 2 rotations give "baaba", 4 rotations give "ababa".
  // The minimum positive rotation for "ababa" is 2.
  // No, the problem asks for the minimum number of rotations to get the *same* string.
  // For "aaaa", 1 rotation gives "aaaa".
  // For "ababa", 2 rotations gives "baaba", 4 rotations gives "ababa".
  // The minimum non-zero k such that is_rotated_equal(s, len, k) is true.
  // If no such k exists in 1..len-1, it means the string is not periodic within its length,
  // or it's periodic with period 1 (all chars same).
  // If it's "aaaa", then k=1 makes it equal.
  // If it's "abcabc", then k=3 makes it equal.
  // The problem implies "minimum number of rotations required to get the same string".
  // This means the smallest k > 0 such that string[i] == string[(i+k)%len] for all i.
  // If string consists of all same characters, e.g., "aaaa", then k=1.
  // If string is "abcabc", then k=3.
  // If string is "abc", then k=3 (full rotation).
  // The result should be the smallest k such that 1 <= k <= len and is_rotated_equal(s, len, k) is true.
  // If k=len, it's always true, so the result is at most len.
  ensures (\exists integer k; 1 <= k <= len && is_rotated_equal(s, len, k) &&
           (\forall integer j; 1 <= j < k ==> !is_rotated_equal(s, len, j))) <==> (\result > 0 && \result <= len);
  ensures (\result > 0 && \result <= len) ==> is_rotated_equal(s, len, \result);
  ensures (\result > 1) ==> (\forall integer j; 1 <= j < \result ==> !is_rotated_equal(s, len, j));
*/
int min_rotations_for_same_string(char *s, int len) {
    /*@
      loop invariant 1 <= k <= len;
      // Invariant: For all rotations `j` less than `k`, `s` rotated by `j` is not equal to `s`.
      loop invariant \forall integer j; 1 <= j < k ==> !is_rotated_equal(s, len, j);
      loop assigns k;
      loop variant len - k;
    */
    for (int k = 1; k <= len; k++) {
        if (is_rotated_equal(s, len, k)) {
            return k;
        }
    }
    // This part should be unreachable given the loop condition and the problem statement
    // (a string rotated by its full length is always equal to itself).
    // However, to satisfy Frama-C, we must return something.
    // The loop will always find a 'k' (at least 'len').
    return len; // Should not be reached, but needed for compilation/completeness.
}
