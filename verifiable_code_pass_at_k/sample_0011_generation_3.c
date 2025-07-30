// Task ID: 11
// Generation: 3

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule I.1: No standard library includes.

  // Axiomatic block for recursive logic to check if a character exists in a string.
  // Rule II.1: Recursive logic for complex properties.
  axiomatic CharInString {
    logic boolean char_in_range(char c, char* s, int start, int end);

    // Rule II.1: Base case for recursive logic.
    axiom char_in_range_base:
      \forall char c, char* s, integer start, end;
        start > end ==> !char_in_range(c, s, start, end);

    // Rule II.1: Recursive step for recursive logic.
    axiom char_in_range_recursive:
      \forall char c, char* s, integer start, end;
        start <= end ==> (char_in_range(c, s, start, end) <==> (s[start] == c || char_in_range(c, s, start + 1, end)));

    // Helper axiom: if a char is in a range, and that range is within a larger one, it's in the larger one.
    // Rule II.2: CRITICAL - Helper Axioms.
    axiom char_in_range_subset:
      \forall char c, char* s, integer start1, end1, start2, end2;
        start1 >= start2 && end1 <= end2 && char_in_range(c, s, start1, end1) ==> char_in_range(c, s, start2, end2);
  }

  // Axiomatic block for finding the first occurrence of a character.
  axiomatic FindFirst {
    logic integer find_first(char c, char* s, int len);

    // Rule II.1: Base case - character not found or empty string.
    axiom find_first_base_not_found:
      \forall char c, char* s, integer len;
        len <= 0 ==> find_first(c, s, len) == -1;

    // Rule II.1: Recursive step - character found at current position.
    axiom find_first_recursive_found:
      \forall char c, char* s, integer len;
        len > 0 && s[0] == c ==> find_first(c, s, len) == 0;

    // Rule II.1: Recursive step - character not found at current position, check rest of string.
    axiom find_first_recursive_not_found:
      \forall char c, char* s, integer len;
        len > 0 && s[0] != c && find_first(c, s + 1, len - 1) != -1 ==> find_first(c, s, len) == 1 + find_first(c, s + 1, len - 1);

    // Rule II.1: Recursive step - character not found in rest of string.
    axiom find_first_recursive_not_found_all:
      \forall char c, char* s, integer len;
        len > 0 && s[0] != c && find_first(c, s + 1, len - 1) == -1 ==> find_first(c, s, len) == -1;

    // Helper axiom: if find_first returns a non-negative index, the character is at that index.
    // Rule II.2: CRITICAL - Helper Axioms.
    axiom find_first_property:
      \forall char c, char* s, integer len, integer idx;
        0 <= idx < len && find_first(c, s, len) == idx ==> s[idx] == c;

    // Helper axiom: if find_first returns -1, the character is not in the string.
    axiom find_first_not_found_property:
      \forall char c, char* s, integer len;
        find_first(c, s, len) == -1 ==> !\exists integer i; 0 <= i < len && s[i] == c;

    // Helper axiom: the returned index is the first one.
    axiom find_first_is_first:
      \forall char c, char* s, integer len, integer idx;
        0 <= idx < len && find_first(c, s, len) == idx ==> \forall integer k; 0 <= k < idx ==> s[k] != c;
  }

  // Axiomatic block for finding the last occurrence of a character.
  axiomatic FindLast {
    logic integer find_last(char c, char* s, int len);

    // Rule II.1: Base case - character not found or empty string.
    axiom find_last_base_not_found:
      \forall char c, char* s, integer len;
        len <= 0 ==> find_last(c, s, len) == -1;

    // Rule II.1: Recursive step - character found at last position.
    axiom find_last_recursive_found:
      \forall char c, char* s, integer len;
        len > 0 && s[len - 1] == c ==> find_last(c, s, len) == len - 1;

    // Rule II.1: Recursive step - character not found at last position, check rest of string.
    axiom find_last_recursive_not_found:
      \forall char c, char* s, integer len;
        len > 0 && s[len - 1] != c && find_last(c, s, len - 1) != -1 ==> find_last(c, s, len) == find_last(c, s, len - 1);

    // Rule II.1: Recursive step - character not found in rest of string.
    axiom find_last_recursive_not_found_all:
      \forall char c, char* s, integer len;
        len > 0 && s[len - 1] != c && find_last(c, s, len - 1) == -1 ==> find_last(c, s, len) == -1;

    // Helper axiom: if find_last returns a non-negative index, the character is at that index.
    // Rule II.2: CRITICAL - Helper Axioms.
    axiom find_last_property:
      \forall char c, char* s, integer len, integer idx;
        0 <= idx < len && find_last(c, s, len) == idx ==> s[idx] == c;

    // Helper axiom: if find_last returns -1, the character is not in the string.
    axiom find_last_not_found_property:
      \forall char c, char* s, integer len;
        find_last(c, s, len) == -1 ==> !\exists integer i; 0 <= i < len && s[i] == c;

    // Helper axiom: the returned index is the last one.
    axiom find_last_is_last:
      \forall char c, char* s, integer len, integer idx;
        0 <= idx < len && find_last(c, s, len) == idx ==> \forall integer k; idx < k < len ==> s[k] != c;
  }
*/

/*@
  requires \valid_read_string(s);
  requires \valid(result + (len - 1)); // Ensure result buffer is large enough
  requires len >= 0;
  // Rule II.5: Prevent potential issues if len is very large, though not directly an overflow.
  // Assumes a reasonable maximum string length.
  requires len < 2000000000; // Arbitrary large but not INT_MAX to avoid issues.

  // The function modifies the result string.
  assigns result[0..len-1];

  // The ensures clause uses the robust logical equivalence pattern (Rule II.3).
  // It states that the result string contains all characters from the original string,
  // except for the first and last occurrences of the character 'c', if they exist.
  ensures (find_first(c, s, len) == -1 || find_last(c, s, len) == -1) ==>
          (\forall integer i; 0 <= i < len ==> result[i] == s[i]); // No removals if c not found or only one occurrence

  ensures (find_first(c, s, len) != -1 && find_last(c, s, len) != -1 && find_first(c, s, len) == find_last(c, s, len)) ==>
          (\forall integer i; 0 <= i < find_first(c, s, len) ==> result[i] == s[i]) &&
          (\forall integer i; find_first(c, s, len) < i < len ==> result[i-1] == s[i]) &&
          result[len-1] == '\0'; // One character removed, string is one shorter

  ensures (find_first(c, s, len) != -1 && find_last(c, s, len) != -1 && find_first(c, s, len) < find_last(c, s, len)) ==>
          (\forall integer i; 0 <= i < find_first(c, s, len) ==> result[i] == s[i]) &&
          (\forall integer i; find_first(c, s, len) < i < find_last(c, s, len) ==> result[i-1] == s[i]) &&
          (\forall integer i; find_last(c, s, len) < i < len ==> result[i-2] == s[i]) &&
          result[len-2] == '\0'; // Two characters removed, string is two shorter

  // The length of the resulting string is reduced by 0, 1, or 2 depending on occurrences.
  ensures (find_first(c, s, len) == -1 || find_last(c, s, len) == -1) ==> \strlen(result) == len;
  ensures (find_first(c, s, len) != -1 && find_last(c, s, len) != -1 && find_first(c, s, len) == find_last(c, s, len)) ==> \strlen(result) == len - 1;
  ensures (find_first(c, s, len) != -1 && find_last(c, s, len) != -1 && find_first(c, s, len) < find_last(c, s, len)) ==> \strlen(result) == len - 2;
*/
void remove_first_last_char(char* s, int len, char c, char* result) {
    int first_idx = -1;
    int last_idx = -1;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i ==> (s[k] != c || first_idx != -1);
      loop invariant first_idx == -1 || (0 <= first_idx < i && s[first_idx] == c && \forall integer k; 0 <= k < first_idx ==> s[k] != c);
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
      loop invariant -1 <= i <= len - 1;
      loop invariant \forall integer k; i < k < len ==> (s[k] != c || last_idx != -1);
      loop invariant last_idx == -1 || (0 <= last_idx < len && s[last_idx] == c && \forall integer k; last_idx < k < len ==> s[k] != c);
      loop assigns i, last_idx;
      loop variant i + 1;
    */
    for (int i = len - 1; i >= 0; i--) {
        if (s[i] == c) {
            last_idx = i;
            break;
        }
    }

    int current_result_idx = 0;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant 0 <= current_result_idx <= i;

      // Invariant capturing the state of the result string construction:
      // Characters before first_idx are copied directly.
      loop invariant (\forall integer k; 0 <= k < i && k < first_idx ==> result[k] == s[k]);
      // Characters between first_idx and last_idx (exclusive) are copied with an offset of 1.
      loop invariant (\forall integer k; first_idx < k < i && k < last_idx ==> result[k - 1] == s[k]);
      // Characters after last_idx are copied with an offset of 2.
      loop invariant (\forall integer k; last_idx < k < i ==> result[k - 2] == s[k]);

      loop assigns i, current_result_idx, result[0..len-1];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (i == first_idx) {
            // Skip the first occurrence
            // If first_idx == last_idx, we only skip this one.
            if (first_idx == last_idx) {
                continue;
            }
        }
        if (i == last_idx) {
            // Skip the last occurrence
            if (first_idx != last_idx) { // Only skip if it's a distinct last occurrence
                continue;
            }
        }
        result[current_result_idx] = s[i];
        current_result_idx++;
    }
    result[current_result_idx] = '\0';
}
