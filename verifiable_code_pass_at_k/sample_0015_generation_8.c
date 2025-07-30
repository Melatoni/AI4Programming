// Task ID: 15
// Generation: 8

/*@ axiomatic LowercaseSplit {
  @   logic boolean is_lowercase(char c) = (c >= 'a' && c <= 'z');

  @   // Recursive logic to define if a segment is split by a lowercase character
  @   // split_by_lowercase(s, start, end) is true if there exists a lowercase
  @   // character in s[start...end-1]
  @   logic boolean split_by_lowercase(char *s, int start, int end) reads s[start..end-1];

  @   axiom split_by_lowercase_base:
  @     \forall char *s, integer start, end;
  @       start >= end ==> !split_by_lowercase(s, start, end);

  @   axiom split_by_lowercase_recursive:
  @     \forall char *s, integer start, end;
  @       start < end ==> (split_by_lowercase(s, start, end) <==>
  @                         (is_lowercase(s[start]) || split_by_lowercase(s, start + 1, end)));

  @   // Helper axiom: if a character is lowercase, then the segment containing it is split.
  @   axiom split_by_lowercase_helper_char:
  @     \forall char *s, integer start, end, i;
  @       start <= i < end && is_lowercase(s[i]) ==> split_by_lowercase(s, start, end);
  @ }
  @*/

/*@
  @ requires \valid_read(s + (0..len-1));
  @ requires len >= 0;
  @
  @ assigns \nothing;
  @
  @ ensures (\exists integer i; 0 <= i < len && is_lowercase(s[i])) <==> (\result == 1);
  @ ensures (\forall integer i; 0 <= i < len ==> !is_lowercase(s[i])) <==> (\result == 0);
  @ ensures split_by_lowercase(s, 0, len) <==> (\result == 1);
  @*/
int split_string_at_lowercase(char *s, int len) {
  /*@
    @ loop invariant 0 <= i <= len;
    @ loop invariant \forall integer k; 0 <= k < i ==> !is_lowercase(s[k]);
    @ loop assigns i;
    @ loop variant len - i;
    @*/
  for (int i = 0; i < len; i++) {
    if (s[i] >= 'a' && s[i] <= 'z') { // Check for lowercase
      return 1; // Found a lowercase character, so the string is "split"
    }
  }
  return 0; // No lowercase characters found
}
