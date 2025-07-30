// Task ID: 18
// Generation: 8

/*@
  // Axiomatic block for recursive logic and helper axioms.
  // Rule II.1: Using axiomatic for complex logic.
  axiomatic CharInString {
    // Predicate: `c` is present in `s` up to index `len-1`
    logic boolean char_present_in_string_rec(char c, char *s, int len) reads s[0..len-1];

    axiom char_present_in_string_rec_base:
      \forall char c, char *s; char_present_in_string_rec(c, s, 0) == \false;

    axiom char_present_in_string_rec_rec:
      \forall char c, char *s, integer len;
        len > 0 ==> char_present_in_string_rec(c, s, len) ==
        (s[len-1] == c || char_present_in_string_rec(c, s, len-1));

    // Helper axiom: If a character is present in a string of length `len`,
    // then it must be present at some index `k < len`.
    // Rule II.2: CRITICAL - Helper Axioms
    axiom char_present_in_string_rec_helper:
      \forall char c, char *s, integer len;
        char_present_in_string_rec(c, s, len) ==> \exists integer k; 0 <= k < len && s[k] == c;

    // Helper axiom: If a character is present at some index `k < len`,
    // then char_present_in_string_rec(c, s, len) is true.
    axiom char_present_in_string_rec_helper_reverse:
      \forall char c, char *s, integer len;
        (\exists integer k; 0 <= k < len && s[k] == c) ==> char_present_in_string_rec(c, s, len);

    // Predicate: `c` is present in `s` (null-terminated)
    logic boolean char_present_in_string(char c, char *s) reads s[0 .. ];

    axiom char_present_in_string_def:
      \forall char c, char *s; char_present_in_string(c, s) == char_present_in_string_rec(c, s, \strlen(s));
  }
*/

/*@
  requires \valid_read(s1);
  requires \valid_read(s2);
  requires \valid(s1 + (0 .. \strlen(s1))); // Ensure s1 is writeable up to its current length
  assigns s1[0 .. \strlen(s1)];

  // The function returns the new length of s1.
  // The characters removed from s1 are those that are present in s2.
  // Rule II.3: Ensures clause for boolean-like functions (though this returns length, it's a good pattern)
  // Here, we define the property of the resulting string.
  ensures \forall integer k; 0 <= k < \result ==> !char_present_in_string(s1[k], s2);
  ensures \forall integer k; 0 <= k < \strlen(\old(s1)) && !char_present_in_string(\old(s1[k]), s2) ==>
          (\exists integer j; 0 <= j < \result && s1[j] == \old(s1[k]));
  ensures \result <= \strlen(\old(s1));
  ensures s1[\result] == '\0'; // Ensure the resulting string is null-terminated
*/
int remove_chars(char *s1, char *s2) {
    int i = 0; // Read pointer for s1
    int j = 0; // Write pointer for s1
    int len_s1 = 0;

    /*@
      loop invariant 0 <= len_s1;
      loop invariant \valid_read(s1 + (0 .. len_s1));
      loop invariant s1[len_s1] == '\0';
      loop assigns len_s1;
      loop variant \strlen(s1) - len_s1;
    */
    for (len_s1 = 0; s1[len_s1] != '\0'; len_s1++) {
        // Compute original length of s1
    }

    /*@
      loop invariant 0 <= i <= len_s1;
      loop invariant 0 <= j <= i;

      // Invariant: All characters s1[0..j-1] are not present in s2.
      loop invariant \forall integer k; 0 <= k < j ==> !char_present_in_string(s1[k], s2);

      // Invariant: All characters from original s1 that are not in s2 and have been processed (up to i)
      // are now in s1[0..j-1].
      loop invariant \forall integer k; 0 <= k < i && !char_present_in_string(\at(s1[k], Pre), s2) ==>
              (\exists integer l; 0 <= l < j && s1[l] == \at(s1[k], Pre));

      loop assigns i, j, s1[0 .. len_s1];
      loop variant len_s1 - i;
    */
    while (i < len_s1) {
        // Rule II.3: Using the logical equivalence pattern in thought process
        // if char_present_in_string(s1[i], s2) == 0 (i.e., not present)
        if (!char_present_in_string(s1[i], s2)) {
            s1[j] = s1[i];
            j++;
        }
        i++;
    }

    s1[j] = '\0'; // Null-terminate the modified string
    return j; // The new length
}
