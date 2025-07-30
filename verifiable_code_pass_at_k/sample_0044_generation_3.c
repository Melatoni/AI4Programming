// Task ID: 44
// Generation: 3

/*@
  // Axiomatic block for recursive logic (Rule II.1)
  axiomatic StringMatch {
    logic integer string_length(char *s);
    axiom string_length_def:
      \forall char *s;
        (string_length(s) == (if *s == '\0' then 0 else 1 + string_length(s + 1)));

    // Helper logic to check if a prefix matches (Rule II.1)
    logic boolean prefix_match_logic(char *str, char *word, integer idx);

    // Base case: If word is exhausted, it matches
    axiom prefix_match_logic_base:
      \forall char *str, char *word, integer idx;
        prefix_match_logic(str, word, idx) <==> (word[idx] == '\0' || (str[idx] != '\0' && str[idx] == word[idx] && prefix_match_logic(str, word, idx + 1)));
  }
*/

/*@
  requires \valid_read(str);
  requires \valid_read(word);
  requires \separated(str + 0..(string_length(str)), word + 0..(string_length(word)));

  // Rule II.5: Prevent out-of-bounds access by ensuring string_length returns a non-negative value
  // and that the strings are null-terminated.
  requires string_length(str) >= 0;
  requires string_length(word) >= 0;

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like return
  ensures (string_length(str) >= string_length(word) && prefix_match_logic(str, word, 0)) <==> (\result == 1);
*/
int starts_with(char *str, char *word) {
    int i = 0;
    /*@
      loop invariant 0 <= i;
      loop invariant str[i] != '\0' || word[i] == '\0'; // Loop terminates if word is exhausted or str is exhausted
      loop invariant \forall integer k; 0 <= k < i ==> str[k] == word[k]; // Prefix matched so far
      loop invariant \valid_read(str + i);
      loop invariant \valid_read(word + i);
      loop assigns i;
      loop variant string_length(word) - i; // Variant for termination (Rule II.4)
    */
    while (word[i] != '\0') {
        if (str[i] == '\0' || str[i] != word[i]) {
            return 0; // Mismatch or end of str before end of word
        }
        i++;
    }
    return 1; // Word fully matched
}
