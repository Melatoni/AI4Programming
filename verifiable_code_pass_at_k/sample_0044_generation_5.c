// Task ID: 44
// Generation: 5

/*@
  // Rule II.1: Define recursive logic for string equality.
  // Rule I.3: Correct pointer type for array parameters.
  axiomatic String {
    logic boolean streq{L}(char *s1, char *s2, int len);

    axiom streq_base{L}:
      \forall char *s1, *s2; streq(s1, s2, 0) == \true;

    axiom streq_recursive{L}:
      \forall char *s1, *s2, integer len;
      len > 0 ==> (streq(s1, s2, len) <==> (s1[len-1] == s2[len-1] && streq(s1, s2, len-1)));

    // Rule II.2: Helper axiom for streq.
    // This helps prove that if two strings are equal up to len, they are also equal up to len-1.
    axiom streq_helper{L}:
      \forall char *s1, *s2, integer len;
      streq(s1, s2, len) ==> streq(s1, s2, len-1);
  }
*/

/*@
  requires \valid_read(str);
  requires \valid_read(word);
  requires len_str >= 0;
  requires len_word >= 0;

  // Rule II.5: Prevent out-of-bounds access.
  requires \forall integer k; 0 <= k < len_str ==> \valid_read(str + k);
  requires \forall integer k; 0 <= k < len_word ==> \valid_read(word + k);

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return.
  ensures (len_str >= len_word && streq(str, word, len_word)) <==> (result == 1);
*/
int matches_prefix(char *str, int len_str, char *word, int len_word) {
    if (len_str < len_word) {
        return 0; // Rule I.2: Use 0 for false.
    }

    /*@
      loop invariant 0 <= i <= len_word;
      // Rule II.4: Invariant capturing the state of the loop.
      loop invariant \forall integer k; 0 <= k < i ==> str[k] == word[k];
      loop assigns i;
      loop variant len_word - i; // Rule II.4: Loop variant for termination.
    */
    for (int i = 0; i < len_word; ++i) {
        if (str[i] != word[i]) {
            return 0; // Rule I.2: Use 0 for false.
        }
    }

    return 1; // Rule I.2: Use 1 for true.
}
