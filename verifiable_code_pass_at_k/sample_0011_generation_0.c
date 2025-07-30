// Task ID: 11
// Generation: 0

char` array (representing a string, null-terminated) and a character `c`, create a new null-terminated `char` array where the first and last occurrences of `c` from the original string are "removed". "Removal" means they are replaced by a special character (e.g., `\0` for simplicity or a placeholder like `_`) in the *new* string, and the remaining characters are shifted to fill the gaps, maintaining relative order. The new string should be placed in a pre-allocated output buffer.

**Further Simplification for Frama-C Verifiability:**
Instead of truly "removing" and shifting, which is very complex to verify for arbitrary string lengths in C without dynamic memory, I will implement a function that populates an output buffer by copying characters from the input string, *skipping* the first and last occurrences of the target character. This means the output string might be shorter and the remaining characters are effectively "shifted" to the left.

Let's define the function signature and behavior:
`int remove_first_last(char *out_s, const char *in_s, int in_len, char c, int out_len_max)`

*   `out_s`: The output buffer where the modified string will be stored.
*   `in_s`: The input string.
*   `in_len`: The length of the input string (excluding null terminator).
*   `c`: The character to remove.
*   `out_len_max`: The maximum capacity of the output buffer, including space for the null terminator.

The function will return `1` if successful (output string fits) and `0` otherwise.

**ACSL Challenges for this Reinterpretation:**
*   **String Lengths:** Defining string length and null termination in ACSL requires careful loop invariants.
*   **Character Skipping:** Proving that exactly the first and last occurrences are skipped, and others are copied, requires precise indexing logic in invariants.
*   **Buffer Overflow:** Ensuring `out_s` is not written beyond `out_len_max`.

Given the complexity of string manipulation and the strict rules for Frama-C, a full, generic string manipulation function with shifting is extremely hard to verify without advanced ACSL features (e.g., `\valid_read`, `\valid_write` for dynamic memory, or more complex ghost code).

For a *verifiable* example that adheres to the spirit of "removing" by skipping and copying to a new buffer, I'll provide a simplified version.

---
Here's the C code with ACSL annotations for a function that copies an input string to an output string, skipping the first and last occurrences of a given character.

/*@
  // Axiomatic block for string length
  axiomatic String {
    logic integer string_length(char *s) reads s;

    axiom string_length_def:
      \forall char *s; string_length(s) == (\exists integer i; s[i] == '\0' && (\forall integer j; 0 <= j < i ==> s[j] != '\0') ? i : -1);
    
    // Helper axiom: If string_length is non-negative, then it's at least 0.
    axiom string_length_non_negative:
      \forall char *s; string_length(s) >= 0 ==> \exists integer i; s[i] == '\0';

    // Helper axiom: If string_length is L, then s[L] is '\0' and s[0..L-1] are not '\0'.
    axiom string_length_value:
      \forall char *s, integer L;
        string_length(s) == L ==> (s[L] == '\0' && (\forall integer k; 0 <= k < L ==> s[k] != '\0'));
  }
*/

/*@
  requires \valid_read_string(in_s);
  requires \valid_write(out_s);
  requires out_len_max >= 0;

  // The output buffer must be large enough to hold the modified string
  // (original length - 2 if two chars are removed, +1 for null terminator).
  // This is a simplification; a more precise check would involve counting
  // occurrences of 'c' first. For this problem, we assume sufficient size.
  requires out_len_max >= string_length(in_s) - 2 + 1; // At least original_len - 2 + null_terminator

  assigns out_s[0..out_len_max-1];

  // The function returns 1 if successful, 0 if output buffer is too small (though
  // the requires clause tries to prevent this).
  ensures (\result == 1) <==>
            (string_length(out_s) <= out_len_max - 1 &&
             (\exists integer first_idx, last_idx;
                0 <= first_idx && first_idx < string_length(in_s) && in_s[first_idx] == c &&
                (\forall integer k; 0 <= k < first_idx ==> in_s[k] != c) && // first_idx is the first occurrence
                0 <= last_idx && last_idx < string_length(in_s) && in_s[last_idx] == c &&
                (\forall integer k; last_idx < k < string_length(in_s) ==> in_s[k] != c) && // last_idx is the last occurrence

                // The output string contains characters from in_s, skipping first_idx and last_idx
                // and keeping relative order.
                // This is very difficult to express formally for all elements and their new positions.
                // A simpler post-condition is to state that the output string is null-terminated
                // and its length is correct based on how many 'c's were found and skipped.
                // For simplicity, we'll focus on the length and null termination.
                // A full "content" proof would require ghost variables or more complex logic.
                string_length(out_s) == string_length(in_s) -
                  (if first_idx == -1 then 0 // No 'c' found
                   else if first_idx == last_idx then 1 // Only one 'c' found
                   else 2) // Two or more 'c's found
            ) ||
            // Case where 'c' is not found in in_s
            (\forall integer k; 0 <= k < string_length(in_s) ==> in_s[k] != c) &&
            string_length(out_s) == string_length(in_s) &&
            (\forall integer k; 0 <= k <= string_length(in_s) ==> out_s[k] == in_s[k])
            );
*/
int remove_first_last(char *out_s, const char *in_s, char c, int out_len_max) {
    int in_len = string_length(in_s);
    int first_idx = -1;
    int last_idx = -1;

    /*@
      loop invariant 0 <= i <= in_len;
      loop invariant (\forall integer k; 0 <= k < i && in_s[k] == c ==> first_idx != -1);
      loop invariant (\forall integer k; 0 <= k < i ==> (in_s[k] == c ? first_idx <= k : \true));
      loop invariant first_idx == -1 || (0 <= first_idx < i && in_s[first_idx] == c && (\forall integer j; 0 <= j < first_idx ==> in_s[j] != c));
      loop assigns i, first_idx;
      loop variant in_len - i;
    */
    for (int i = 0; i < in_len; i++) {
        if (in_s[i] == c) {
            if (first_idx == -1) {
                first_idx = i;
            }
        }
    }

    /*@
      loop invariant 0 <= i <= in_len;
      loop invariant (\forall integer k; i < k < in_len && in_s[k] == c ==> last_idx != -1);
      loop invariant (\forall integer k; i < k < in_len ==> (in_s[k] == c ? last_idx >= k : \true));
      loop invariant last_idx == -1 || (i <= last_idx < in_len && in_s[last_idx] == c && (\forall integer j; last_idx < j < in_len ==> in_s[j] != c));
      loop assigns i, last_idx;
      loop variant i;
    */
    for (int i = in_len - 1; i >= 0; i--) {
        if (in_s[i] == c) {
            if (last_idx == -1) {
                last_idx = i;
            }
        }
    }

    int out_idx = 0;
    /*@
      loop invariant 0 <= i <= in_len;
      loop invariant 0 <= out_idx <= i;
      loop invariant out_idx <= out_len_max - 1; // Ensure we don't write past out_len_max-1 for null terminator
      loop invariant (\forall integer k; 0 <= k < i && k != first_idx && k != last_idx ==>
                          (\exists integer j; 0 <= j < out_idx && out_s[j] == in_s[k])); // Characters before i are copied if not skipped
      loop invariant (\forall integer k; 0 <= k < out_idx ==>
                          (\exists integer j; 0 <= j < i && j != first_idx && j != last_idx && out_s[k] == in_s[j])); // Characters in out_s came from in_s and were not skipped
      loop assigns i, out_idx, out_s[0..out_len_max-1];
      loop variant in_len - i;
    */
    for (int i = 0; i < in_len; i++) {
        if (i == first_idx && first_idx != -1) { // Skip first occurrence
            first_idx = -1; // Mark as skipped to handle cases where first_idx == last_idx
            continue;
        }
        if (i == last_idx && last_idx != -1) { // Skip last occurrence
            last_idx = -1; // Mark as skipped
            continue;
        }

        if (out_idx >= out_len_max - 1) { // Check for buffer overflow before writing
            out_s[0] = '\0'; // Ensure out_s is null-terminated even on error
            return 0; // Output buffer too small
        }
        out_s[out_idx] = in_s[i];
        out_idx++;
    }

    if (out_idx >= out_len_max) { // Final check for null terminator space
        out_s[0] = '\0';
        return 0;
    }
    out_s[out_idx] = '\0'; // Null-terminate the output string

    return 1; // Success
}
