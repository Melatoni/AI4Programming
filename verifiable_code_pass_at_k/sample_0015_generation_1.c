// Task ID: 15
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1, II.2: Recursive logic for complexity, helper axioms.
  // Define an axiomatic block for character properties
  axiomatic CharProperties {
    logic int is_lowercase_char(char c);

    axiom is_lowercase_char_def_true:
      \forall char c; ('a' <= c && c <= 'z') ==> is_lowercase_char(c) == 1;
    axiom is_lowercase_char_def_false:
      \forall char c; !('a' <= c && c <= 'z') ==> is_lowercase_char(c) == 0;
  }

  // Define an axiomatic block for string properties
  axiomatic StringProperties {
    // Helper function to check if a character at index i is a split point
    logic int is_split_point(char *s, int len, int i);
    axiom is_split_point_def:
      \forall char *s, int len, int i;
        (0 <= i && i < len && is_lowercase_char(s[i]) == 1) ==> is_split_point(s, len, i) == 1;
    axiom is_split_point_def_false:
      \forall char *s, int len, int i;
        !(0 <= i && i < len && is_lowercase_char(s[i]) == 1) ==> is_split_point(s, len, i) == 0;

    // Helper function to count the number of split points up to an index
    logic integer count_split_points_up_to(char *s, int len, int index);

    axiom count_split_points_up_to_base:
      \forall char *s, int len; count_split_points_up_to(s, len, -1) == 0;

    axiom count_split_points_up_to_recursive:
      \forall char *s, int len, int index;
        (0 <= index && index < len) ==>
          count_split_points_up_to(s, len, index) ==
            count_split_points_up_to(s, len, index - 1) + is_split_point(s, len, index);

    // Helper axiom: The total count of split points is non-negative
    axiom total_split_points_non_negative:
      \forall char *s, int len;
        (len >= 0) ==> count_split_points_up_to(s, len, len - 1) >= 0;

    // Helper axiom: Count up to index is bounded by index + 1
    axiom count_split_points_up_to_upper_bound:
      \forall char *s, int len, int index;
        (0 <= index && index < len) ==> count_split_points_up_to(s, len, index) <= index + 1;
  }
*/

/*@
  requires \valid_read(s + (0..len - 1));
  requires len >= 0;
  requires \valid_write(out_indices + (0..len)); // out_indices can hold up to len+1 elements (len splits + 1 for end)

  assigns out_indices[0..len];

  // Rule II.3: Ensures clause for boolean-like functions
  ensures \forall integer k; (0 <= k < \result) ==>
                                (0 <= out_indices[k] < len && is_split_point(s, len, out_indices[k]) == 1 &&
                                 (\forall integer j; (0 <= j < k) ==> out_indices[j] < out_indices[k]));

  ensures \result == count_split_points_up_to(s, len, len - 1);

  // ensures that all split points are captured
  ensures \forall integer i; (0 <= i < len && is_split_point(s, len, i) == 1) ==>
                                (\exists integer k; (0 <= k < \result) && out_indices[k] == i);

  // ensures that no non-split points are captured
  ensures \forall integer k; (0 <= k < \result) ==> is_split_point(s, len, out_indices[k]) == 1;

  // ensures that the output array is sorted
  ensures \forall integer k1, k2; (0 <= k1 < k2 < \result) ==> out_indices[k1] < out_indices[k2];
*/
int split_string_at_lowercase(char *s, int len, int *out_indices) {
    int count = 0;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant 0 <= count <= i;
      // Rule II.4: Loop invariant for `out_indices`
      loop invariant \forall integer k; (0 <= k < count) ==>
                                        (0 <= out_indices[k] < i && is_split_point(s, len, out_indices[k]) == 1 &&
                                         (\forall integer j; (0 <= j < k) ==> out_indices[j] < out_indices[k]));
      // Loop invariant: ensures that `count` correctly reflects the number of split points found so far
      loop invariant count == count_split_points_up_to(s, len, i - 1);

      loop assigns i, count, out_indices[0..len];
      // Rule II.4: Loop variant for termination
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Rule I.2: Use int for boolean logic
        if (is_lowercase_char(s[i]) == 1) {
            // Rule II.5: Prevent RTE - out_indices access
            // This is implicitly handled by the requires clause on out_indices size.
            // Further, the loop invariant `count <= i` and `i < len` implies `count < len`,
            // so `out_indices[count]` is always within `out_indices[0..len-1]` or `out_indices[0..len]`.
            // The ensures clause for the function indicates `\result` can be up to `len`,
            // meaning `out_indices[\result-1]` could be the last written index.
            // The size `len+1` for `out_indices` covers this.
            out_indices[count] = i;
            count++;
        }
    }
    return count;
}
