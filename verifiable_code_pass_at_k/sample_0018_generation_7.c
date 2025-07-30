// Task ID: 18
// Generation: 7

/*@ axiomatic CharInString {
  @   logic boolean char_in_string(char c, char *s, int len);

  @   axiom char_in_string_empty{L}:
  @     \forall char c, char *s; char_in_string(c, s, 0) == \false;

  @   axiom char_in_string_recursive{L}:
  @     \forall char c, char *s, integer len;
  @       len > 0 ==> (char_in_string(c, s, len) <==> (s[len-1] == c || char_in_string(c, s, len-1)));
  @ }
  @*/

/*@
  @ requires \valid(s1 + (0..len1-1));
  @ requires \valid(s2 + (0..len2-1));
  @ requires len1 >= 0;
  @ requires len2 >= 0;
  @ requires \separated(s1 + (0..len1-1), s2 + (0..len2-1));
  @
  @ assigns s1[0..len1-1];
  @
  @ ensures \result >= 0 && \result <= len1;
  @ ensures \forall integer i; 0 <= i < \result ==> !char_in_string(s1[i], s2, len2);
  @ ensures \forall integer i, j; 0 <= i < \result && 0 <= j < len1 && i < j ==> \old(s1[j]) == s1[j]; // Not modified beyond new_len
  @ ensures \forall integer i; 0 <= i < \result ==> \exists integer k; 0 <= k < len1 && \old(s1[k]) == s1[i] && !char_in_string(\old(s1[k]), s2, len2);
  @*/
int remove_chars(char *s1, int len1, char *s2, int len2) {
    int write_idx = 0;
    /*@
      @ loop invariant 0 <= read_idx <= len1;
      @ loop invariant 0 <= write_idx <= read_idx;
      @ loop invariant \forall integer i; 0 <= i < write_idx ==> !char_in_string(s1[i], s2, len2);
      @ loop invariant \forall integer i; 0 <= i < write_idx ==> \exists integer k; 0 <= k < read_idx && \old(s1[k]) == s1[i] && !char_in_string(\old(s1[k]), s2, len2);
      @ loop invariant \forall integer i; write_idx <= i < read_idx ==> char_in_string(\old(s1[i]), s2, len2);
      @ loop invariant \forall integer i, j; write_idx <= i < j < read_idx ==> \old(s1[j]) == s1[j]; // Not modified yet
      @ loop assigns read_idx, write_idx, s1[0..len1-1];
      @ loop variant len1 - read_idx;
    */
    for (int read_idx = 0; read_idx < len1; read_idx++) {
        /*@
          @ assigns \nothing;
          @ ensures \result == 1 <==> char_in_string(s1[read_idx], s2, len2);
        */
        int current_char_in_s2 = 0;
        /*@
          @ loop invariant 0 <= k <= len2;
          @ loop invariant current_char_in_s2 == 1 <==> (\exists integer j; 0 <= j < k && s2[j] == s1[read_idx]);
          @ loop assigns k, current_char_in_s2;
          @ loop variant len2 - k;
        */
        for (int k = 0; k < len2; k++) {
            if (s1[read_idx] == s2[k]) {
                current_char_in_s2 = 1;
                break;
            }
        }

        if (current_char_in_s2 == 0) {
            s1[write_idx] = s1[read_idx];
            write_idx++;
        }
    }
    return write_idx;
}
