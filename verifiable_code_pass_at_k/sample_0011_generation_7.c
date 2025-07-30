// Task ID: 11
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define recursive logic for string properties.
  // Helper for string length, assuming null termination.
  axiomatic String {
    logic integer string_length(char *s);

    axiom string_length_nil:
      \forall char *s; s[0] == '\0' ==> string_length(s) == 0;
    axiom string_length_cons:
      \forall char *s; s[0] != '\0' ==> string_length(s) == 1 + string_length(s + 1);
  }

  // Helper to find the first occurrence of a character.
  // Returns -1 if not found.
  axiomatic FirstOcc {
    logic integer first_occurrence(char *s, int len, char c);

    axiom first_occurrence_base_not_found:
      \forall char *s, integer len, char c;
        len == 0 ==> first_occurrence(s, len, c) == -1;
    axiom first_occurrence_base_found:
      \forall char *s, integer len, char c;
        len > 0 && s[0] == c ==> first_occurrence(s, len, c) == 0;
    axiom first_occurrence_recursive:
      \forall char *s, integer len, char c;
        len > 0 && s[0] != c ==>
          first_occurrence(s, len, c) == (if first_occurrence(s + 1, len - 1, c) == -1
                                          then -1
                                          else 1 + first_occurrence(s + 1, len - 1, c));
  }

  // Helper to find the last occurrence of a character.
  // Returns -1 if not found.
  axiomatic LastOcc {
    logic integer last_occurrence(char *s, int len, char c);

    axiom last_occurrence_base_not_found:
      \forall char *s, integer len, char c;
        len == 0 ==> last_occurrence(s, len, c) == -1;
    axiom last_occurrence_base_found:
      \forall char *s, integer len, char c;
        len > 0 && s[len - 1] == c ==> last_occurrence(s, len, c) == len - 1;
    axiom last_occurrence_recursive:
      \forall char *s, integer len, char c;
        len > 0 && s[len - 1] != c ==>
          last_occurrence(s, len, c) == (if last_occurrence(s, len - 1, c) == -1
                                         then -1
                                         else last_occurrence(s, len - 1, c));
  }
*/

/*@
  requires \valid_read(s);
  requires \valid(result);
  requires \separated(s + (0..string_length(s)), result + (0..string_length(s)));
  requires string_length(s) >= 0;
  // Rule II.5: Ensure result buffer is large enough.
  requires \valid(result + (0..string_length(s)));

  assigns result[0..string_length(s)];

  // The core logic of the function.
  // Let L be the length of the input string s.
  // Let first_idx be the index of the first occurrence of c in s.
  // Let last_idx be the index of the last occurrence of c in s.

  // Case 1: Character c is not found in s.
  // In this case, the result string should be identical to s.
  ensures (first_occurrence(s, string_length(s), c) == -1) ==>
          (\forall integer k; 0 <= k <= string_length(s) ==> result[k] == s[k]);

  // Case 2: Character c is found, but first and last occurrences are the same.
  // e.g., "banana", c = 'b'. first = 0, last = 0.
  // In this case, the result string should have the character at this index removed.
  ensures (first_occurrence(s, string_length(s), c) != -1 &&
           first_occurrence(s, string_length(s), c) == last_occurrence(s, string_length(s), c)) ==>
          (string_length(result) == string_length(s) - 1 &&
           \forall integer k; 0 <= k < first_occurrence(s, string_length(s), c) ==> result[k] == s[k] &&
           \forall integer k; first_occurrence(s, string_length(s), c) <= k < string_length(result) ==> result[k] == s[k+1]);

  // Case 3: Character c is found, and first and last occurrences are different.
  // e.g., "abracadabra", c = 'a'. first = 0, last = 10.
  // In this case, the result string should have characters at first_idx and last_idx removed.
  ensures (first_occurrence(s, string_length(s), c) != -1 &&
           first_occurrence(s, string_length(s), c) != last_occurrence(s, string_length(s), c)) ==>
          (string_length(result) == string_length(s) - 2 &&
           \forall integer k; 0 <= k < first_occurrence(s, string_length(s), c) ==> result[k] == s[k] &&
           \forall integer k; first_occurrence(s, string_length(s), c) <= k < last_occurrence(s, string_length(s), c) - 1 ==> result[k] == s[k+1] &&
           \forall integer k; last_occurrence(s, string_length(s), c) - 1 <= k < string_length(result) ==> result[k] == s[k+2]);
*/
void remove_first_last_char(char *s, char c, char *result) {
    int len = 0;
    /*@
      loop invariant 0 <= len <= string_length(s);
      loop invariant \forall integer k; 0 <= k < len ==> s[k] != '\0';
      loop assigns len;
      loop variant string_length(s) - len;
    */
    while (s[len] != '\0') {
        len++;
    }

    int first_idx = -1;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant (first_idx == -1) <==> (\forall integer k; 0 <= k < i ==> s[k] != c);
      loop invariant (first_idx != -1) ==> (0 <= first_idx < i && s[first_idx] == c && \forall integer k; 0 <= k < first_idx ==> s[k] != c);
      loop assigns i, first_idx;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (s[i] == c) {
            first_idx = i;
            break;
        }
    }

    // If character not found, copy original string and return.
    if (first_idx == -1) {
        /*@
          loop invariant 0 <= i <= len;
          loop invariant \forall integer k; 0 <= k < i ==> result[k] == s[k];
          loop assigns i, result[0..len];
          loop variant len - i;
        */
        for (int i = 0; i <= len; i++) { // Copy null terminator too
            result[i] = s[i];
        }
        return;
    }

    int last_idx = -1;
    /*@
      loop invariant -1 <= i < len;
      loop invariant (last_idx == -1) <==> (\forall integer k; i < k < len ==> s[k] != c);
      loop invariant (last_idx != -1) ==> (i < last_idx < len && s[last_idx] == c && \forall integer k; last_idx < k < len ==> s[k] != c);
      loop assigns i, last_idx;
      loop variant i;
    */
    for (int i = len - 1; i >= 0; i--) {
        if (s[i] == c) {
            last_idx = i;
            break;
        }
    }

    // If first and last are the same, we only remove one occurrence.
    if (first_idx == last_idx) {
        int res_idx = 0;
        /*@
          loop invariant 0 <= i <= len;
          loop invariant 0 <= res_idx <= i;
          loop invariant res_idx == i - (if i > first_idx then 1 else 0);
          loop invariant \forall integer k; 0 <= k < res_idx ==> result[k] == s[k + (if k >= first_idx then 1 else 0)];
          loop assigns i, res_idx, result[0..len];
          loop variant len - i;
        */
        for (int i = 0; i <= len; i++) {
            if (i == first_idx) {
                // Skip this character
            } else {
                result[res_idx] = s[i];
                res_idx++;
            }
        }
    } else { // First and last are different.
        int res_idx = 0;
        /*@
          loop invariant 0 <= i <= len;
          loop invariant 0 <= res_idx <= i;
          loop invariant res_idx == i - (if i > first_idx then 1 else 0) - (if i > last_idx then 1 else 0) ;
          loop invariant \forall integer k; 0 <= k < res_idx ==>
            result[k] == s[k + (if k >= first_idx then 1 else 0) + (if k >= last_idx - 1 then 1 else 0)];
          loop assigns i, res_idx, result[0..len];
          loop variant len - i;
        */
        for (int i = 0; i <= len; i++) {
            if (i == first_idx || i == last_idx) {
                // Skip these characters
            } else {
                result[res_idx] = s[i];
                res_idx++;
            }
        }
    }
}
