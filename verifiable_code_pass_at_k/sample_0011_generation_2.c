// Task ID: 11
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Define an axiomatic block for string properties.
  axiomatic StringProperties {
    logic int string_length_logic{L}(char *s, int max_len) reads s;

    axiom string_length_ax1{L}:
      \forall char *s, int max_len;
        (max_len == 0) ==> (string_length_logic(s, max_len) == 0);

    axiom string_length_ax2{L}:
      \forall char *s, int max_len;
        (max_len > 0 && s[0] == '\0') ==> (string_length_logic(s, max_len) == 0);

    axiom string_length_ax3{L}:
      \forall char *s, int max_len;
        (max_len > 0 && s[0] != '\0') ==> (string_length_logic(s, max_len) == 1 + string_length_logic(s + 1, max_len - 1));

    logic int first_occurrence_logic{L}(char *s, int len, char c) reads s;

    axiom first_occurrence_ax1{L}:
      \forall char *s, int len, char c;
        (len <= 0) ==> (first_occurrence_logic(s, len, c) == -1);

    axiom first_occurrence_ax2{L}:
      \forall char *s, int len, char c;
        (len > 0 && s[0] == c) ==> (first_occurrence_logic(s, len, c) == 0);

    axiom first_occurrence_ax3{L}:
      \forall char *s, int len, char c;
        (len > 0 && s[0] != c) ==>
          (first_occurrence_logic(s, len, c) ==
           (if first_occurrence_logic(s + 1, len - 1, c) == -1
            then -1
            else 1 + first_occurrence_logic(s + 1, len - 1, c)));

    logic int last_occurrence_logic{L}(char *s, int len, char c) reads s;

    axiom last_occurrence_ax1{L}:
      \forall char *s, int len, char c;
        (len <= 0) ==> (last_occurrence_logic(s, len, c) == -1);

    axiom last_occurrence_ax2{L}:
      \forall char *s, int len, char c;
        (len > 0) ==>
          (last_occurrence_logic(s, len, c) ==
           (if s[len - 1] == c
            then len - 1
            else last_occurrence_logic(s, len - 1, c)));

    // Rule II.2: Helper axioms for string_length_logic
    axiom string_length_non_negative{L}:
      \forall char *s, int max_len; string_length_logic(s, max_len) >= 0;

    axiom string_length_bounded{L}:
      \forall char *s, int max_len; string_length_logic(s, max_len) <= max_len;

    // Helper axiom for first_occurrence_logic
    axiom first_occurrence_range{L}:
      \forall char *s, int len, char c;
        (first_occurrence_logic(s, len, c) != -1) ==>
          (0 <= first_occurrence_logic(s, len, c) < len);

    // Helper axiom for last_occurrence_logic
    axiom last_occurrence_range{L}:
      \forall char *s, int len, char c;
        (last_occurrence_logic(s, len, c) != -1) ==>
          (0 <= last_occurrence_logic(s, len, c) < len);

    // Axiom to relate first and last occurrence
    axiom first_last_relation{L}:
      \forall char *s, int len, char c;
        (first_occurrence_logic(s, len, c) != -1 && last_occurrence_logic(s, len, c) != -1) ==>
          (first_occurrence_logic(s, len, c) <= last_occurrence_logic(s, len, c));
  }
*/

/*@
  requires \valid_read(s);
  requires \valid_write(result);
  requires max_len >= 0;
  requires \strlen(s) < max_len; // Ensure s is null-terminated within max_len
  requires \strlen(result) == 0; // result is an empty buffer initially
  requires \separated(s + (0..max_len-1), result + (0..max_len-1)); // No overlap between source and destination

  assigns result[0..max_len-1];

  // Rule II.3: Ensures clause for boolean-like functions. Not applicable here as it returns void.
  // Instead, describe the post-state of 'result'.
  ensures string_length_logic(result, max_len) ==
          (if first_occurrence_logic(s, string_length_logic(s, max_len), c) == -1
           then string_length_logic(s, max_len)
           else
             (if first_occurrence_logic(s, string_length_logic(s, max_len), c) == last_occurrence_logic(s, string_length_logic(s, max_len), c)
              then string_length_logic(s, max_len) - 2
              else string_length_logic(s, max_len) - 2
             )
          );

  ensures (first_occurrence_logic(s, string_length_logic(s, max_len), c) == -1) ==>
            (\forall integer k; 0 <= k <= string_length_logic(s, max_len) ==> result[k] == s[k]);

  ensures (first_occurrence_logic(s, string_length_logic(s, max_len), c) != -1 &&
           first_occurrence_logic(s, string_length_logic(s, max_len), c) == last_occurrence_logic(s, string_length_logic(s, max_len), c)) ==>
            (\forall integer k; 0 <= k < first_occurrence_logic(s, string_length_logic(s, max_len), c) ==> result[k] == s[k]) &&
            (\forall integer k; first_occurrence_logic(s, string_length_logic(s, max_len), c) < k <= string_length_logic(s, max_len) ==> result[k-1] == s[k]); // Shifted for single removal

  ensures (first_occurrence_logic(s, string_length_logic(s, max_len), c) != -1 &&
           first_occurrence_logic(s, string_length_logic(s, max_len), c) != last_occurrence_logic(s, string_length_logic(s, max_len), c)) ==>
            (\forall integer k; 0 <= k < first_occurrence_logic(s, string_length_logic(s, max_len), c) ==> result[k] == s[k]) &&
            (\forall integer k; first_occurrence_logic(s, string_length_logic(s, max_len), c) < k < last_occurrence_logic(s, string_length_logic(s, max_len), c) ==> result[k-1] == s[k]) &&
            (\forall integer k; last_occurrence_logic(s, string_length_logic(s, max_len), c) < k <= string_length_logic(s, max_len) ==> result[k-2] == s[k]); // Shifted for double removal

  ensures result[string_length_logic(result, max_len)] == '\0';
*/
void remove_first_last_char(char *s, char c, char *result, int max_len) {
    int len = 0;
    /*@
      loop invariant 0 <= len <= max_len;
      loop invariant \forall integer k; 0 <= k < len ==> s[k] != '\0';
      loop invariant s[len] == '\0' || len == max_len;
      loop assigns len;
      loop variant max_len - len;
    */
    while (len < max_len && s[len] != '\0') {
        len++;
    }

    int first_idx = -1;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant -1 <= first_idx < i;
      loop invariant (\forall integer k; 0 <= k < i && first_idx == -1 ==> s[k] != c);
      loop invariant (first_idx != -1) ==> (\exists integer k; 0 <= k < i && s[k] == c && (\forall integer j; 0 <= j < k ==> s[j] != c) && first_idx == k);
      loop assigns i, first_idx;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (s[i] == c) {
            first_idx = i;
            break;
        }
    }

    int last_idx = -1;
    /*@
      loop invariant -1 <= last_idx < len;
      loop invariant 0 <= i <= len;
      loop invariant (\forall integer k; i <= k < len && last_idx == -1 ==> s[k] != c);
      loop invariant (last_idx != -1) ==> (\exists integer k; i <= k < len && s[k] == c && (\forall integer j; k < j < len ==> s[j] != c) && last_idx == k);
      loop assigns i, last_idx;
      loop variant i;
    */
    for (int i = len - 1; i >= 0; i--) {
        if (s[i] == c) {
            last_idx = i;
            break;
        }
    }

    if (first_idx == -1) {
        // Character not found, copy original string
        /*@
          loop invariant 0 <= i <= len;
          loop invariant \forall integer k; 0 <= k < i ==> result[k] == s[k];
          loop assigns i, result[0..len-1];
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            result[i] = s[i];
        }
        result[len] = '\0';
    } else {
        int current_result_idx = 0;
        /*@
          loop invariant 0 <= i <= len;
          loop invariant 0 <= current_result_idx <= i;
          loop invariant (\forall integer k; 0 <= k < i && k != first_idx && k != last_idx ==> result[current_result_idx - ( (k > first_idx ? 1 : 0) + (k > last_idx ? 1 : 0) ) ] == s[k]);
          loop invariant (first_idx == last_idx && i > first_idx) ==> current_result_idx == i - 1;
          loop invariant (first_idx != last_idx && i > first_idx && i > last_idx) ==> current_result_idx == i - 2;
          loop invariant (first_idx != last_idx && i > first_idx && i <= last_idx) ==> current_result_idx == i - 1;
          loop invariant (first_idx != last_idx && i <= first_idx) ==> current_result_idx == i;
          loop assigns i, current_result_idx, result[0..max_len-1];
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            if (i == first_idx || i == last_idx) {
                // Skip this character
            } else {
                result[current_result_idx] = s[i];
                current_result_idx++;
            }
        }
        result[current_result_idx] = '\0';
    }
}
