// Task ID: 43
// Generation: 3

/*@ axiomatic RegexMatcher {
  @   // Rule II.1: Recursive logic for complex properties.
  @   // Checks if a character is a lowercase letter.
  @   logic boolean is_lower_char(char c) = (c >= 'a' && c <= 'z');
  @ 
  @   // Checks if a substring from start to end (inclusive) consists only of lowercase letters.
  @   // Rule II.1: Recursive logic for complex properties.
  @   logic boolean is_lower_sequence(char *s, integer start, integer end) =
  @     (start > end) ||
  @     (is_lower_char(s[start]) && is_lower_sequence(s, start + 1, end));
  @ 
  @   // Helper axiom for is_lower_sequence: if a sequence is lower, all its chars are lower.
  @   // Rule II.2: Critical helper axioms.
  @   axiom is_lower_sequence_helper:
  @     \forall char *s, integer start, integer end;
  @       is_lower_sequence(s, start, end) ==>
  @         \forall integer k; start <= k <= end ==> is_lower_char(s[k]);
  @ 
  @   // Helper axiom for is_lower_sequence: if a sequence is lower, its length is non-negative.
  @   // Rule II.2: Critical helper axioms.
  @   axiom is_lower_sequence_length_helper:
  @     \forall char *s, integer start, integer end;
  @       is_lower_sequence(s, start, end) ==> (end - start + 1) >= 0;
  @ 
  @   // Helper axiom for is_lower_sequence: if a sequence is empty, it's a lower sequence.
  @   // Rule II.2: Critical helper axioms.
  @   axiom is_lower_sequence_empty_helper:
  @     \forall char *s, integer start, integer end;
  @       start > end ==> is_lower_sequence(s, start, end);
  @ }
  @*/

/*@
  @ requires \valid_read(str + (0..len - 1));
  @ requires len >= 0;
  @ requires \forall integer k; 0 <= k < len ==> \valid_read(str+k);
  @
  @ assigns \nothing;
  @
  @ // Rule II.3: Ensures clause uses logical equivalence.
  @ // The function returns 1 if there exists a sequence of lowercase letters,
  @ // followed by an underscore, followed by another sequence of lowercase letters.
  @ ensures (\exists integer i, j, k;
  @          0 <= i && i <= j && j < k && k < len && // Indices are valid and ordered
  @          is_lower_sequence(str, i, j) &&        // First part is lowercase sequence
  @          str[j+1] == '_' &&                     // Separated by an underscore
  @          is_lower_sequence(str, j+2, k)         // Second part is lowercase sequence
  @         ) <==> (\result == 1);
  @*/
int find_regex_sequence(char *str, int len) {
  /*@
    @ loop invariant 0 <= i <= len;
    @ loop invariant \forall integer x, y, z;
    @   0 <= x <= y && y < z && z < i &&
    @   is_lower_sequence(str, x, y) && str[y+1] == '_' && is_lower_sequence(str, y+2, z)
    @   ==> \result == 1; // If a match was found before i, result is 1.
    @ loop assigns i;
    @ loop variant len - i;
  */
  for (int i = 0; i < len; i++) {
    // Find the start of the first lowercase sequence
    /*@
      @ loop invariant 0 <= i <= start_first <= len;
      @ loop invariant \forall integer k; i <= k < start_first ==> !is_lower_char(str[k]);
      @ loop assigns start_first;
      @ loop variant len - start_first;
    */
    int start_first = i;
    while (start_first < len && !('a' <= str[start_first] && str[start_first] <= 'z')) {
      start_first++;
    }

    // If no lowercase char found, continue
    if (start_first >= len) {
      break;
    }

    // Find the end of the first lowercase sequence
    /*@
      @ loop invariant start_first <= end_first < len;
      @ loop invariant is_lower_sequence(str, start_first, end_first);
      @ loop assigns end_first;
      @ loop variant len - end_first;
    */
    int end_first = start_first;
    while (end_first + 1 < len && ('a' <= str[end_first + 1] && str[end_first + 1] <= 'z')) {
      end_first++;
    }

    // Check for underscore
    if (end_first + 1 < len && str[end_first + 1] == '_') {
      // Find the start of the second lowercase sequence
      int start_second = end_first + 2;

      // If there's no character after the underscore, or it's not lowercase, continue
      if (start_second >= len || !('a' <= str[start_second] && str[start_second] <= 'z')) {
          // Rule III.4: No stray semicolons.
          // No op, just continue to next i
      } else {
        // Find the end of the second lowercase sequence
        /*@
          @ loop invariant start_second <= end_second < len;
          @ loop invariant is_lower_sequence(str, start_second, end_second);
          @ loop assigns end_second;
          @ loop variant len - end_second;
        */
        int end_second = start_second;
        while (end_second + 1 < len && ('a' <= str[end_second + 1] && str[end_second + 1] <= 'z')) {
          end_second++;
        }
        // Found a match: [first_seq]_[second_seq]
        /*@ assert is_lower_sequence(str, start_first, end_first); */
        /*@ assert str[end_first+1] == '_'; */
        /*@ assert is_lower_sequence(str, start_second, end_second); */
        return 1; // Rule I.2: Use 1 for true.
      }
    }
    i = end_first; // Advance i to avoid re-checking characters already part of a sequence
  }
  return 0; // Rule I.2: Use 0 for false.
}
