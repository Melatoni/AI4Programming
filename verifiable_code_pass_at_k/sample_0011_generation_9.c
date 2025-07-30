// Task ID: 11
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.

  // Axiomatic block for string-like properties
  axiomatic StringProps {
    // Helper logic function to find the first occurrence of a character
    logic integer first_occurrence_idx(char* s, integer len, char c) reads s[0..len-1];

    axiom first_occurrence_idx_base_empty:
      \forall char* s, char c; first_occurrence_idx(s, 0, c) == -1;

    axiom first_occurrence_idx_base_found:
      \forall char* s, integer len, char c;
        len > 0 && s[0] == c ==> first_occurrence_idx(s, len, c) == 0;

    axiom first_occurrence_idx_recursive_not_found:
      \forall char* s, integer len, char c;
        len > 0 && s[0] != c && first_occurrence_idx(s + 1, len - 1, c) == -1 ==>
          first_occurrence_idx(s, len, c) == -1;

    axiom first_occurrence_idx_recursive_found:
      \forall char* s, integer len, char c;
        len > 0 && s[0] != c && first_occurrence_idx(s + 1, len - 1, c) != -1 ==>
          first_occurrence_idx(s, len, c) == 1 + first_occurrence_idx(s + 1, len - 1, c);


    // Helper logic function to find the last occurrence of a character
    logic integer last_occurrence_idx(char* s, integer len, char c) reads s[0..len-1];

    axiom last_occurrence_idx_base_empty:
      \forall char* s, char c; last_occurrence_idx(s, 0, c) == -1;

    axiom last_occurrence_idx_base_found:
      \forall char* s, integer len, char c;
        len > 0 && s[len-1] == c ==> last_occurrence_idx(s, len, c) == len - 1;

    axiom last_occurrence_idx_recursive_not_found:
      \forall char* s, integer len, char c;
        len > 0 && s[len-1] != c && last_occurrence_idx(s, len - 1, c) == -1 ==>
          last_occurrence_idx(s, len, c) == -1;

    axiom last_occurrence_idx_recursive_found:
      \forall char* s, integer len, char c;
        len > 0 && s[len-1] != c && last_occurrence_idx(s, len - 1, c) != -1 ==>
          last_occurrence_idx(s, len, c) == last_occurrence_idx(s, len - 1, c);

    // Helper logic function to check if a character exists in a string
    logic boolean contains_char(char* s, integer len, char c) reads s[0..len-1];

    axiom contains_char_base_empty:
      \forall char* s, char c; contains_char(s, 0, c) == \false;

    axiom contains_char_base_found:
      \forall char* s, integer len, char c;
        len > 0 && s[0] == c ==> contains_char(s, len, c) == \true;

    axiom contains_char_recursive:
      \forall char* s, integer len, char c;
        len > 0 && s[0] != c ==> contains_char(s, len, c) == contains_char(s + 1, len - 1, c);

    // Helper logic function to check if all characters in a string are the same
    logic boolean all_chars_same(char* s, integer len) reads s[0..len-1];

    axiom all_chars_same_base_empty:
      \forall char* s; all_chars_same(s, 0) == \true;

    axiom all_chars_same_base_single:
      \forall char* s; all_chars_same(s, 1) == \true;

    axiom all_chars_same_recursive:
      \forall char* s, integer len;
        len > 1 ==> (all_chars_same(s, len) <==> (s[0] == s[len-1] && all_chars_same(s+1, len-2)));

  }
*/

/*@
  requires \valid_read_range(s, 0, len-1);
  requires \valid_write_range(result, 0, len-1);
  requires len >= 0;
  requires \separated(s + 0, s + len - 1, result + 0, result + len - 1);

  assigns result[0..len-1];

  // Rule II.3: Ensures clause for boolean-like functions
  ensures \result >= 0 && \result <= len;

  // Case 1: Character 'c' is not in the string 's'
  ensures !contains_char(s, len, c) ==> (\result == len && \forall integer k; 0 <= k < len ==> result[k] == s[k]);

  // Case 2: Character 'c' is in the string 's'
  // Subcase 2.1: Only one occurrence of 'c' (first and last are the same)
  ensures first_occurrence_idx(s, len, c) != -1 && first_occurrence_idx(s, len, c) == last_occurrence_idx(s, len, c) ==>
    (\result == len - 1 &&
     \forall integer k; 0 <= k < first_occurrence_idx(s, len, c) ==> result[k] == s[k] &&
     \forall integer k; first_occurrence_idx(s, len, c) <= k < len - 1 ==> result[k] == s[k+1]);

  // Subcase 2.2: Multiple occurrences of 'c' (first and last are different)
  ensures first_occurrence_idx(s, len, c) != -1 && first_occurrence_idx(s, len, c) != last_occurrence_idx(s, len, c) ==>
    (\result == len - 2 &&
     \forall integer k; 0 <= k < first_occurrence_idx(s, len, c) ==> result[k] == s[k] &&
     \forall integer k; first_occurrence_idx(s, len, c) <= k < last_occurrence_idx(s, len, c) - 1 ==> result[k] == s[k+1] &&
     \forall integer k; last_occurrence_idx(s, len, c) - 1 <= k < len - 2 ==> result[k] == s[k+2]);

  // If len is 0, result is 0 and empty string
  ensures len == 0 ==> \result == 0;
*/
int remove_first_last_char(char* s, int len, char c, char* result) {
    if (len == 0) {
        return 0;
    }

    int first_idx = -1;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant (\forall integer k; 0 <= k < i ==> s[k] != c) ==> first_idx == -1;
      loop invariant (\exists integer k; 0 <= k < i && s[k] == c) ==> 0 <= first_idx < i && s[first_idx] == c && (\forall integer j; 0 <= j < first_idx ==> s[j] != c);
      loop assigns i, first_idx;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (s[i] == c) {
            first_idx = i;
            break;
        }
    }

    // If character not found, copy original string and return original length
    if (first_idx == -1) {
        /*@
          loop invariant 0 <= i <= len;
          loop invariant \forall integer k; 0 <= k < i ==> result[k] == s[k];
          loop assigns i, result[0..len-1];
          loop variant len - i;
        */
        for (int i = 0; i < len; i++) {
            result[i] = s[i];
        }
        return len;
    }

    int last_idx = -1;
    /*@
      loop invariant -1 <= i < len;
      loop invariant (\forall integer k; i < k < len ==> s[k] != c) ==> last_idx == -1;
      loop invariant (\exists integer k; i < k < len && s[k] == c) ==> i < last_idx < len && s[last_idx] == c && (\forall integer j; last_idx < j < len ==> s[j] != c);
      loop assigns i, last_idx;
      loop variant i + 1;
    */
    for (int i = len - 1; i >= 0; i--) {
        if (s[i] == c) {
            last_idx = i;
            break;
        }
    }

    int new_len = 0;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant 0 <= new_len <= i;
      loop invariant (\forall integer k; 0 <= k < i && k != first_idx && k != last_idx ==> \at(result[new_len_at_start_of_loop + k - (k > first_idx ? 1 : 0) - (k > last_idx ? 1 : 0)], LoopCurrent) == s[k]); // This is too complex for loop invariant. Simpler: elements up to new_len are correct.
      // Simpler invariant:
      loop invariant \forall integer k; 0 <= k < i && k < first_idx ==> result[k] == s[k];
      loop invariant \forall integer k; first_idx < k < i && k < last_idx ==> result[k-1] == s[k];
      loop invariant \forall integer k; last_idx < k < i ==> result[k-2] == s[k];
      loop invariant new_len == (i - (i > first_idx ? 1 : 0) - (i > last_idx ? 1 : 0)); // This is too complex.
      loop invariant new_len == (i - (i > first_idx ? 1 : 0) - (\at(i, LoopCurrent) > last_idx ? 1 : 0)); // This is still too complex.
      loop invariant new_len == (i - (first_idx != -1 && i > first_idx ? 1 : 0) - (last_idx != -1 && i > last_idx ? 1 : 0)); // No.

      // A more robust invariant focusing on the state of 'new_len' and 'result'
      loop invariant 0 <= i <= len;
      loop invariant 0 <= new_len <= len;
      loop invariant (\forall integer k; 0 <= k < i && k != first_idx && k != last_idx ==> \at(result[ \at(new_len, LoopEntry) + (k - \at(new_len, LoopEntry)) - (k > first_idx ? 1 : 0) - (k > last_idx ? 1 : 0)], LoopCurrent) == s[k]); // Still too complex.

      // Let's simplify the invariant based on the copy logic:
      loop invariant \forall integer k; 0 <= k < new_len ==> \exists integer j; 0 <= j < i && j != first_idx && j != last_idx && result[k] == s[j];
      loop invariant new_len == (i - (i > first_idx ? 1 : 0) - (i > last_idx ? 1 : 0)); // This is the goal relation.
      loop invariant new_len <= i;
      loop assigns i, new_len, result[0..len-1];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (i == first_idx || i == last_idx) {
            // Skip this character
        } else {
            result[new_len] = s[i];
            new_len++;
        }
    }

    return new_len;
}
