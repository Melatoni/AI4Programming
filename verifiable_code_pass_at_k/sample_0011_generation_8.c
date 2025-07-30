// Task ID: 11
// Generation: 8

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule II.5: Add requires clauses to prevent overflows and ensure valid input.
  // The string length must be non-negative.
  requires len >= 0;
  // The string pointer must be valid for the given length.
  requires \valid_read(s + (0..len-1));
  // The output buffer must be valid and large enough.
  requires \valid_write(out + (0..len-1));
  // The output buffer must not overlap with the input string.
  requires \separated(s + (0..len-1), out + (0..len-1));

  // The function computes the new length of the string after removal.
  assigns out[0..len-1];

  // Rule II.3: The ensures clause uses logical equivalence for boolean-like results.
  // It states that the result (new length) is correct, and the content of 'out' is as expected.
  ensures \result >= 0 && \result <= len;
  ensures \forall integer k; 0 <= k < \result ==>
    // If the character 'c' is not found, the string is copied as is.
    // Otherwise, the first and last occurrences are removed.
    (
      (\forall integer i; 0 <= i < len ==> s[i] != c) ==>
      (out[k] == s[k] && \result == len)
    )
    &&
    (
      (\exists integer first_idx; 0 <= first_idx < len && s[first_idx] == c) ==>
      (
        // The characters before the first occurrence are copied.
        (\exists integer first_idx, last_idx;
          0 <= first_idx < len && s[first_idx] == c &&
          (\forall integer i; 0 <= i < first_idx ==> s[i] != c) &&
          0 <= last_idx < len && s[last_idx] == c &&
          (\forall integer i; last_idx < i < len ==> s[i] != c) &&
          first_idx <= last_idx;
          (
            (first_idx > k) ==> out[k] == s[k]
          )
          &&
          (
            // Characters between first_idx and last_idx, excluding them, are shifted.
            (k >= first_idx && k < last_idx - 1) ==> out[k] == s[k+1]
          )
          &&
          (
            // Characters after last_idx are shifted by 2.
            (k >= last_idx - 1) ==> out[k] == s[k+2]
          )
        )
      )
    );
*/
int remove_first_last_char(char s[], int len, char c, char out[]) {
    int first_idx = -1;
    int last_idx = -1;

    /*@
      loop invariant 0 <= i && i <= len;
      loop invariant (\forall integer k; 0 <= k < i ==> s[k] != c) ==> (first_idx == -1);
      loop invariant (\exists integer k; 0 <= k < i && s[k] == c) ==> (0 <= first_idx < i && s[first_idx] == c && (\forall integer j; 0 <= j < first_idx ==> s[j] != c));
      loop assigns i, first_idx;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (s[i] == c) {
            first_idx = i;
            break;
        }
    }

    /*@
      loop invariant -1 <= i && i < len; // i can be -1 before the loop
      loop invariant (\forall integer k; i < k < len ==> s[k] != c) ==> (last_idx == -1);
      loop invariant (\exists integer k; i < k < len && s[k] == c) ==> (0 <= last_idx < len && s[last_idx] == c && (\forall integer j; last_idx < j < len ==> s[j] != c));
      loop assigns i, last_idx;
      loop variant i + 1;
    */
    for (int i = len - 1; i >= 0; i--) {
        if (s[i] == c) {
            last_idx = i;
            break;
        }
    }

    if (first_idx == -1) {
        // Character not found, copy the string as is
        /*@
          loop invariant 0 <= i && i <= len;
          loop invariant \forall integer k; 0 <= k < i ==> out[k] == s[k];
          loop assigns i, out[0..len-1];
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            out[i] = s[i];
        }
        return len;
    } else {
        // Character found, remove first and last occurrences
        int new_len = 0;
        /*@
          loop invariant 0 <= i && i <= len;
          loop invariant 0 <= new_len && new_len <= i;
          loop invariant \forall integer k; 0 <= k < new_len ==>
            (k < first_idx ==> out[k] == s[k]) &&
            (k >= first_idx && k < last_idx - 1 ==> out[k] == s[k+1]) &&
            (k >= last_idx - 1 ==> out[k] == s[k+2]);
          loop assigns i, new_len, out[0..len-1];
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            if (i == first_idx || i == last_idx) {
                // Skip this character
                // No operation, just move to the next character in s
            } else {
                // Copy the character to the new string
                out[new_len] = s[i];
                new_len++;
            }
        }
        return new_len;
    }
}
