// Task ID: 7
// Generation: 6

/*@ axiomatic WordLength {
  @   logic integer word_length(char *s, integer start_idx) ;

  @   axiom word_length_base:
  @     \forall char *s, integer start_idx;
  @       (s[start_idx] == '\0' || s[start_idx] == ' ' || s[start_idx] == '\t' || s[start_idx] == '\n' || s[start_idx] == '\r') ==> word_length(s, start_idx) == 0;

  @   axiom word_length_recursive:
  @     \forall char *s, integer start_idx;
  @       (s[start_idx] != '\0' && s[start_idx] != ' ' && s[start_idx] != '\t' && s[start_idx] != '\n' && s[start_idx] != '\r') ==> word_length(s, start_idx) == 1 + word_length(s, start_idx + 1);

  @   // Helper axiom (Rule II.2): If a word has length >= 4, it means it's not empty and the next part has length >= 3.
  @   axiom word_length_ge4_helper:
  @     \forall char *s, integer start_idx;
  @       word_length(s, start_idx) >= 4 ==> (s[start_idx] != '\0' && s[start_idx] != ' ' && s[start_idx] != '\t' && s[start_idx] != '\n' && s[start_idx] != '\r');

  @   // Helper axiom (Rule II.2): If a word has length >= 4, it means it's not empty and the next part has length >= 3.
  @   axiom word_length_ge4_helper_recursive:
  @     \forall char *s, integer start_idx;
  @       word_length(s, start_idx) >= 4 ==> word_length(s, start_idx+1) >= 3;
  @ }
  */

/*@
  @ requires \valid_read(s + (0..\strlen(s)));
  @ requires \valid_write(result_indices + (0..max_results - 1));
  @ requires max_results >= 0;
  @ ensures \forall integer i; 0 <= i < \result ==> 0 <= result_indices[i] < \strlen(s);
  @ ensures \forall integer i; 0 <= i < \result ==> word_length(s, result_indices[i]) >= 4;
  @ ensures \forall integer i; 0 <= i < \result ==>
  @           (result_indices[i] == 0 || s[result_indices[i]-1] == ' ' || s[result_indices[i]-1] == '\t' || s[result_indices[i]-1] == '\n' || s[result_indices[i]-1] == '\r');
  @ ensures \forall integer i; 0 <= i < \result ==>
  @           (s[result_indices[i]] != ' ' && s[result_indices[i]] != '\t' && s[result_indices[i]] != '\n' && s[result_indices[i]] != '\r' && s[result_indices[i]] != '\0');
  @ ensures \result <= max_results;
  @ assigns result_indices[0..max_results-1];
  */
int find_long_words(char *s, int result_indices[], int max_results) {
    int count = 0;
    int i = 0;

    /*@
      @ loop invariant 0 <= i <= \strlen(s);
      @ loop invariant 0 <= count <= max_results;
      @ loop invariant \forall integer k; 0 <= k < count ==> 0 <= result_indices[k] < \strlen(s);
      @ loop invariant \forall integer k; 0 <= k < count ==> word_length(s, result_indices[k]) >= 4;
      @ loop invariant \forall integer k; 0 <= k < count ==>
      @                  (result_indices[k] == 0 || s[result_indices[k]-1] == ' ' || s[result_indices[k]-1] == '\t' || s[result_indices[k]-1] == '\n' || s[result_indices[k]-1] == '\r');
      @ loop invariant \forall integer k; 0 <= k < count ==>
      @                  (s[result_indices[k]] != ' ' && s[result_indices[k]] != '\t' && s[result_indices[k]] != '\n' && s[result_indices[k]] != '\r' && s[result_indices[k]] != '\0');
      @ loop variant \strlen(s) - i;
      @ assigns i, count, result_indices[0..max_results-1];
      */
    while (s[i] != '\0') {
        // Skip leading whitespace
        /*@
          @ loop invariant i <= \strlen(s);
          @ loop invariant \forall integer k; \at(i, Pre) <= k < i ==> (s[k] == ' ' || s[k] == '\t' || s[k] == '\n' || s[k] == '\r');
          @ loop variant \strlen(s) - i;
          @ assigns i;
          */
        while (s[i] == ' ' || s[i] == '\t' || s[i] == '\n' || s[i] == '\r') {
            i++;
        }

        if (s[i] == '\0') {
            break; // End of string after whitespace
        }

        // Now `i` points to the start of a potential word
        int word_start = i;
        int current_word_length = 0;

        /*@
          @ loop invariant word_start <= i <= \strlen(s);
          @ loop invariant current_word_length == i - word_start;
          @ loop invariant \forall integer k; word_start <= k < i ==>
          @   (s[k] != ' ' && s[k] != '\t' && s[k] != '\n' && s[k] != '\r' && s[k] != '\0');
          @ loop variant \strlen(s) - i;
          @ assigns i, current_word_length;
          */
        while (s[i] != '\0' && s[i] != ' ' && s[i] != '\t' && s[i] != '\n' && s[i] != '\r') {
            current_word_length++;
            i++;
        }

        // Check if the word length is at least 4 and we have space in the results array
        if (current_word_length >= 4 && count < max_results) {
            result_indices[count] = word_start;
            count++;
        }
    }

    return count;
}
