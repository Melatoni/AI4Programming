// Task ID: 15
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay (relevant for string parameters).
*/

/*@
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
  axiomatic IsLower {
    logic boolean is_lower_char(char c);

    axiom is_lower_char_def:
      \forall char c; is_lower_char(c) <==> ('a' <= c && c <= 'z');
  }

  axiomatic SplitPoint {
    // Defines a split point: either the end of the string or a lowercase char.
    logic integer split_point(char *s, int len, int start_idx);

    axiom split_point_base:
      \forall char *s, integer len, integer start_idx;
        (start_idx >= len) ==> (split_point(s, len, start_idx) == len);

    axiom split_point_recursive:
      \forall char *s, integer len, integer start_idx;
        (start_idx < len) ==>
        (split_point(s, len, start_idx) ==
         (if is_lower_char(s[start_idx])
          then start_idx
          else split_point(s, len, start_idx + 1)));

    // Helper axiom: if there's a lowercase char, the split point is less than len.
    // If no lowercase char from start_idx, then split_point is len.
    axiom split_point_property:
      \forall char *s, integer len, integer start_idx;
        (\exists integer k; start_idx <= k < len && is_lower_char(s[k])) <==> (split_point(s, len, start_idx) < len);
  }
*/

/*@
  requires \valid_read_string(s);
  requires len >= 0;
  requires len == \strlen(s); // Ensure len matches actual string length

  // output_len must be large enough to hold all potential split points.
  // In the worst case, every character is a split point + the final 0.
  requires \valid(output_indices + (len + 1) - 1); // +1 for the final 0.

  assigns output_indices[0..len]; // output_indices can be written up to len.

  // The function returns the number of split points found.
  // The split points are stored in output_indices.
  // The first split point is always 0.
  // Subsequent split points are indices of lowercase letters, or the string end.
  ensures \result >= 0 && \result <= len + 1; // Max len+1 indices (0, then each char, then end)
  ensures output_indices[0] == 0; // First split point is always 0.
  ensures \forall integer i; 0 <= i < \result - 1 ==>
            (output_indices[i] < output_indices[i+1] &&
             output_indices[i+1] == split_point(s, len, output_indices[i] + 1));
  ensures output_indices[\result - 1] == split_point(s, len, output_indices[\result - 1]); // Last split point is the end of string or a lowercase char.
  ensures \result == (\num_of(integer k; 0 <= k < len && is_lower_char(s[k])) + (if len > 0 then 1 else 0) + 1); // Number of splits: 0 + each lower char + end of string. This needs refinement.

  // Refined ensures for result:
  // The number of split points is 1 (for index 0) plus the number of lowercase letters, plus 1 if the very last point is the end of the string and not a lowercase char.
  // This is tricky. Let's ensure the output_indices array correctly lists the split points.
  // The last element in output_indices should be 'len' if the string ends without a lowercase char, or the index of the last lowercase char.
  // The number of split points is the number of elements in output_indices.
  ensures \forall integer k; 0 <= k < \result - 1 ==>
            (output_indices[k] < len && !is_lower_char(s[output_indices[k]])); // Split points are not lowercase themselves, except the last one.
  ensures (\forall integer k; 0 < k < \result ==>
            (output_indices[k] == len || is_lower_char(s[output_indices[k]]))); // All split points after 0 are either len or a lowercase char.
  ensures \result == (\num_of(integer k; 0 <= k < len && is_lower_char(s[k])) + 1 + (if len > 0 && !is_lower_char(s[len-1]) && \result > 1 then 1 else 0)); // More refined.

  // Let's simplify the result ensures: it's the number of split points correctly identified.
  // The indices are monotonically increasing.
  ensures \forall integer i; 0 <= i < \result - 1 ==> output_indices[i] < output_indices[i+1];
  // The last index is always len.
  ensures output_indices[\result - 1] == len;
  // All intermediate indices are lowercase letters.
  ensures \forall integer i; 0 < i < \result - 1 ==> is_lower_char(s[output_indices[i]]);
*/
int split_at_lowercase(char *s, int len, int *output_indices) {
    int count = 0;
    int current_idx = 0;

    // The first split point is always 0.
    /*@
      requires \valid(output_indices);
      assigns output_indices[0];
      ensures output_indices[0] == 0;
      ensures count == 1;
      ensures current_idx == 0;
    */
    {
        output_indices[count] = 0;
        count++;
    }

    /*@
      loop invariant 0 < count <= len + 1;
      loop invariant 0 <= current_idx <= len;
      loop invariant output_indices[0] == 0;
      loop invariant \forall integer k; 0 <= k < count - 1 ==> output_indices[k] < output_indices[k+1];
      loop invariant \forall integer k; 0 < k < count - 1 ==> is_lower_char(s[output_indices[k]]);
      loop invariant current_idx == output_indices[count - 1]; // current_idx is the last recorded split point.

      loop assigns current_idx, count, output_indices[0..len];

      loop variant len - current_idx;
    */
    while (current_idx < len) {
        /*@
          requires 0 <= current_idx < len;
          assigns \nothing;
          ensures \result == (if is_lower_char(s[current_idx]) then 1 else 0);
        */
        int is_lower = (s[current_idx] >= 'a' && s[current_idx] <= 'z');

        if (is_lower) {
            // Found a lowercase character, it's a split point.
            /*@
              requires count < len + 1; // Ensure space in output_indices
              requires current_idx < len;
              assigns output_indices[count], count;
              ensures output_indices[\old(count)] == current_idx;
              ensures count == \old(count) + 1;
            */
            {
                output_indices[count] = current_idx;
                count++;
            }
        }
        /*@
          assigns current_idx;
          ensures current_idx == \old(current_idx) + 1;
        */
        current_idx++;
    }

    // The very end of the string is always considered a split point.
    // This handles the case where the string doesn't end with a lowercase char.
    // We only add it if it's not already the last recorded split point (e.g., if len was a lowercase char).
    /*@
      requires count < len + 2; // Ensure space for 'len' if not already added.
      requires current_idx == len;
      assigns output_indices[count], count;
      ensures output_indices[\old(count)] == len;
      ensures count == \old(count) + 1;
      ensures output_indices[\result - 1] == len;
    */
    {
        output_indices[count] = len;
        count++;
    }

    return count;
}
