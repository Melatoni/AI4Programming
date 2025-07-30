// Task ID: 11
// Generation: 6

/*@
  // Rule I.2: Use int for boolean return type.
  // Rule I.1: No standard libraries.
  // Rule II.5: Preconditions to prevent runtime errors (e.g., negative length, invalid index access).
  requires \valid_read(s + (0..len - 1));
  requires len >= 0;
  requires \valid_write(result + (0..len - 1)); // result buffer must be large enough
  requires \separated(s + (0..len - 1), result + (0..len - 1));

  // Axiomatic block for recursive logic to find the first and last occurrences.
  // Rule II.1: Use recursive logic for complex properties.
  // Rule I.3: Array parameters decay to pointers.
  axiomatic CharOccurrences {
    logic integer first_occurrence_idx{L}(char *s, integer len, char c) reads s[0..len-1];
    logic integer last_occurrence_idx{L}(char *s, integer len, char c) reads s[0..len-1];

    axiom first_occurrence_base{L}:
      \forall char *s, integer len, char c;
        (len == 0 || (len > 0 && s[0] != c)) ==> first_occurrence_idx(s, len, c) == -1;

    axiom first_occurrence_recursive_found{L}:
      \forall char *s, integer len, char c;
        len > 0 && s[0] == c ==> first_occurrence_idx(s, len, c) == 0;

    axiom first_occurrence_recursive_not_found{L}:
      \forall char *s, integer len, char c;
        len > 0 && s[0] != c && first_occurrence_idx(s + 1, len - 1, c) == -1 ==> first_occurrence_idx(s, len, c) == -1;

    axiom first_occurrence_recursive_found_later{L}:
      \forall char *s, integer len, char c;
        len > 0 && s[0] != c && first_occurrence_idx(s + 1, len - 1, c) != -1 ==> first_occurrence_idx(s, len, c) == 1 + first_occurrence_idx(s + 1, len - 1, c);
    
    // Rule II.2: Helper axioms for first_occurrence_idx
    axiom first_occurrence_idx_range{L}:
      \forall char *s, integer len, char c;
        first_occurrence_idx(s, len, c) != -1 ==> 0 <= first_occurrence_idx(s, len, c) < len;

    logic integer find_first_idx(char *s, integer len, char c) reads s[0..len-1];
    axiom find_first_idx_def:
      \forall char *s, integer len, char c;
        find_first_idx(s, len, c) == first_occurrence_idx(s, len, c);

    axiom last_occurrence_base{L}:
      \forall char *s, integer len, char c;
        (len == 0 || (len > 0 && s[len - 1] != c)) ==> last_occurrence_idx(s, len, c) == -1;

    axiom last_occurrence_recursive_found{L}:
      \forall char *s, integer len, char c;
        len > 0 && s[len - 1] == c ==> last_occurrence_idx(s, len, c) == len - 1;

    axiom last_occurrence_recursive_not_found{L}:
      \forall char *s, integer len, char c;
        len > 0 && s[len - 1] != c && last_occurrence_idx(s, len - 1, c) == -1 ==> last_occurrence_idx(s, len, c) == -1;

    axiom last_occurrence_recursive_found_earlier{L}:
      \forall char *s, integer len, char c;
        len > 0 && s[len - 1] != c && last_occurrence_idx(s, len - 1, c) != -1 ==> last_occurrence_idx(s, len, c) == last_occurrence_idx(s, len - 1, c);

    // Rule II.2: Helper axioms for last_occurrence_idx
    axiom last_occurrence_idx_range{L}:
      \forall char *s, integer len, char c;
        last_occurrence_idx(s, len, c) != -1 ==> 0 <= last_occurrence_idx(s, len, c) < len;

    logic integer find_last_idx(char *s, integer len, char c) reads s[0..len-1];
    axiom find_last_idx_def:
      \forall char *s, integer len, char c;
        find_last_idx(s, len, c) == last_occurrence_idx(s, len, c);
  }

  // assigns clause: Specifies what memory locations the function might modify.
  // The result buffer is written to, so it must be mentioned here.
  assigns result[0..len-1];

  // ensures clause: Postconditions for the function.
  // The function returns the new length of the string.
  // Rule II.3: For boolean-like results, use <==>. Here, the result is the new length.
  // We need to ensure the correct characters are copied and the new length is correct.
  ensures \result >= 0 && \result <= len;
  ensures \forall integer k; 0 <= k < \result ==>
              // Characters before first_idx and after last_idx are removed.
              // Characters between first_idx and last_idx remain, shifted left.
              (find_first_idx(s, len, c) == -1 || find_last_idx(s, len, c) == -1) ==>
                  (\forall integer i; 0 <= i < len ==> result[i] == s[i] && \result == len);
  ensures (find_first_idx(s, len, c) != -1 && find_last_idx(s, len, c) != -1) ==>
              // Case 1: First and last occurrences are the same.
              (find_first_idx(s, len, c) == find_last_idx(s, len, c) ==>
                  (\forall integer i; 0 <= i < find_first_idx(s, len, c) ==> result[i] == s[i]) &&
                  (\forall integer i; find_first_idx(s, len, c) <= i < len - 1 ==> result[i] == s[i+1]) &&
                  \result == len - 1
              );
  ensures (find_first_idx(s, len, c) != -1 && find_last_idx(s, len, c) != -1) ==>
              // Case 2: First and last occurrences are different.
              (find_first_idx(s, len, c) != find_last_idx(s, len, c) ==>
                  (\forall integer i; 0 <= i < find_first_idx(s, len, c) ==> result[i] == s[i]) &&
                  (\forall integer i; find_first_idx(s, len, c) <= i < find_last_idx(s, len, c) - 1 ==> result[i] == s[i+1]) &&
                  (\forall integer i; find_last_idx(s, len, c) - 1 <= i < len - 2 ==> result[i] == s[i+2]) &&
                  \result == len - 2
              );
*/
int remove_first_last_char(char *s, int len, char c, char *result) {
    int first_idx = -1;
    int last_idx = -1;
    int i;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i ==> s[k] != c;
      loop invariant first_idx == -1;
      loop assigns i, first_idx;
      loop variant len - i;
    */
    for (i = 0; i < len; i++) {
        if (s[i] == c) {
            first_idx = i;
            break;
        }
    }

    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; i < k < len ==> s[k] != c;
      loop invariant last_idx == -1;
      loop assigns i, last_idx;
      loop variant i;
    */
    for (i = len - 1; i >= 0; i--) {
        if (s[i] == c) {
            last_idx = i;
            break;
        }
    }

    int current_result_idx = 0;

    if (first_idx == -1) {
        // Character not found, copy original string.
        /*@
          loop invariant 0 <= i <= len;
          loop invariant 0 <= current_result_idx == i <= len;
          loop invariant \forall integer k; 0 <= k < i ==> result[k] == s[k];
          loop assigns i, current_result_idx, result[0..len-1];
          loop variant len - i;
        */
        for (i = 0; i < len; i++) {
            result[current_result_idx] = s[i];
            current_result_idx++;
        }
        return len;
    } else {
        if (first_idx == last_idx) {
            // Only one occurrence of the character. Remove it.
            /*@
              loop invariant 0 <= i <= len;
              loop invariant 0 <= current_result_idx <= i;
              loop invariant \forall integer k; 0 <= k < i;
                (k < first_idx ==> result[k] == s[k]) &&
                (k >= first_idx ==> result[k] == s[k+1]);
              loop assigns i, current_result_idx, result[0..len-1];
              loop variant len - i;
            */
            for (i = 0; i < len; i++) {
                if (i == first_idx) {
                    // Skip this character
                } else {
                    result[current_result_idx] = s[i];
                    current_result_idx++;
                }
            }
            return len - 1;
        } else {
            // First and last occurrences are different. Remove both.
            /*@
              loop invariant 0 <= i <= len;
              loop invariant 0 <= current_result_idx <= i;
              loop invariant \forall integer k; 0 <= k < i;
                (k < first_idx ==> result[k] == s[k]) &&
                (first_idx < k < last_idx ==> result[k-1] == s[k]) &&
                (k > last_idx ==> result[k-2] == s[k]);
              loop assigns i, current_result_idx, result[0..len-1];
              loop variant len - i;
            */
            for (i = 0; i < len; i++) {
                if (i == first_idx || i == last_idx) {
                    // Skip these characters
                } else {
                    result[current_result_idx] = s[i];
                    current_result_idx++;
                }
            }
            return len - 2;
        }
    }
}
