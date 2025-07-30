// Task ID: 44
// Generation: 1

/*@
  // Rule I.2: Use int for boolean return.
  // Rule II.3: Use logical equivalence for boolean-like functions.
  // Rule II.5: Prevent RTE by ensuring string and word are not NULL and have valid lengths.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: No spaces around '..'.
  
  // Axiomatic block for character comparison logic.
  // Rule II.1: Use recursive logic for properties over sequences.
  // Rule II.2: Helper axioms for recursive functions are critical.
  
  axiomatic CharComparison {
    logic boolean is_char_equal(char c1, char c2) = (c1 == c2);

    // Recursive logic to check if a prefix of s1 matches a prefix of s2.
    // len is the length of the prefixes to compare.
    logic boolean is_prefix_equal(char *s1, char *s2, int len);

    axiom is_prefix_equal_base:
      \forall char *s1, *s2;
        is_prefix_equal(s1, s2, 0) == \true;

    axiom is_prefix_equal_rec:
      \forall char *s1, *s2, integer len;
        len > 0 ==>
        (is_prefix_equal(s1, s2, len) == (is_char_equal(s1[len-1], s2[len-1]) && is_prefix_equal(s1, s2, len - 1)));
        
    // Helper axiom: If all characters are equal up to len, then for any k < len, they are also equal up to k.
    axiom is_prefix_equal_helper_subset:
      \forall char *s1, *s2, integer len, integer k;
        0 <= k <= len && is_prefix_equal(s1, s2, len) ==> is_prefix_equal(s1, s2, k);
  }
*/

/*@
  requires \valid_read(str);
  requires \valid_read(word);
  requires \separated(str+0..\strlen(str), word+0..\strlen(word)); // Ensure no overlap
  requires \strlen(word) <= \strlen(str); // Word cannot be longer than string to be a prefix.
  
  assigns \nothing;
  
  ensures (\result == 1) <==> (is_prefix_equal(str, word, \strlen(word)));
*/
int match_word_at_beginning(char *str, char *word) {
    /*@
      loop invariant 0 <= i <= \strlen(word);
      loop invariant \forall integer k; 0 <= k < i ==> str[k] == word[k];
      loop invariant is_prefix_equal(str, word, i); // Express the invariant using the axiomatic function
      loop assigns i;
      loop variant \strlen(word) - i;
    */
    for (int i = 0; i < \strlen(word); i++) {
        if (str[i] != word[i]) {
            return 0; // Mismatch found
        }
    }
    return 1; // All characters matched
}
