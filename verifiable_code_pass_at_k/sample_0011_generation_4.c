// Task ID: 11
// Generation: 4

/*@ axiomatic CharOccurrence {
  @   logic integer first_occurrence_idx(char *s, int len, int c);
  @   axiom first_occurrence_idx_base:
  @     \forall char *s, int len, int c;
  @       len <= 0 ==> first_occurrence_idx(s, len, c) == -1;
  @   axiom first_occurrence_idx_recursive_found:
  @     \forall char *s, int len, int c;
  @       len > 0 && s[0] == c ==> first_occurrence_idx(s, len, c) == 0;
  @   axiom first_occurrence_idx_recursive_not_found:
  @     \forall char *s, int len, int c;
  @       len > 0 && s[0] != c ==> first_occurrence_idx(s, len, c) == (if first_occurrence_idx(s + 1, len - 1, c) == -1 then -1 else first_occurrence_idx(s + 1, len - 1, c) + 1);
  @
  @   logic integer last_occurrence_idx(char *s, int len, int c);
  @   axiom last_occurrence_idx_base:
  @     \forall char *s, int len, int c;
  @       len <= 0 ==> last_occurrence_idx(s, len, c) == -1;
  @   axiom last_occurrence_idx_recursive_found:
  @     \forall char *s, int len, int c;
  @       len > 0 && s[len - 1] == c ==> last_occurrence_idx(s, len, c) == len - 1;
  @   axiom last_occurrence_idx_recursive_not_found:
  @     \forall char *s, int len, int c;
  @       len > 0 && s[len - 1] != c ==> last_occurrence_idx(s, len, c) == last_occurrence_idx(s, len - 1, c);
  @ }
*/

/*@
  requires \valid(s + (0..len-1));
  requires \valid(result + (0..len-1));
  requires len >= 0;
  // Ensures null termination for non-empty strings if original was null-terminated.
  requires len > 0 ==> s[len-1] == '\0'; 
  assigns result[0..len-1];

  // Rule II.3: Ensures clause for boolean-like function (implicit return via result string)
  ensures \forall integer k; 0 <= k < len;
    (k < first_occurrence_idx(s, len, c) || k > last_occurrence_idx(s, len, c)) ==> result[k] == s[k];
  ensures \forall integer k; 0 <= k < len;
    (first_occurrence_idx(s, len, c) == -1 || k == first_occurrence_idx(s, len, c) || k == last_occurrence_idx(s, len, c)) ==> result[k] == (k < len ? (len > 0 ? '\0' : '\0') : '\0'); // Using '\0' as a placeholder for removed char
*/
void remove_first_last_char(char *s, int len, char c, char *result) {
    int first_idx = -1;
    int last_idx = -1;

    if (len <= 0) {
        return;
    }

    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i;
        s[k] != c ==> first_idx == -1 || first_idx == \at(first_idx, Pre);
      loop invariant (first_idx == -1) <==> (\forall integer k; 0 <= k < i; s[k] != c);
      loop invariant (first_idx != -1) ==> (0 <= first_idx < i && s[first_idx] == c && \forall integer k; 0 <= k < first_idx; s[k] != c);
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
      loop invariant -1 <= i < len;
      loop invariant \forall integer k; i < k < len;
        s[k] != c ==> last_idx == -1 || last_idx == \at(last_idx, Pre);
      loop invariant (last_idx == -1) <==> (\forall integer k; i < k < len; s[k] != c); // This is tricky, last_idx is only set if char found.
      loop invariant (last_idx != -1) ==> (i < last_idx < len && s[last_idx] == c && \forall integer k; last_idx < k < len; s[k] != c);
      loop assigns i, last_idx;
      loop variant i;
    */
    for (int i = len - 1; i >= 0; i--) {
        if (s[i] == c) {
            last_idx = i;
            break;
        }
    }

    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i;
        (k != first_idx && k != last_idx) ==> result[k] == s[k];
      loop invariant \forall integer k; 0 <= k < i;
        (k == first_idx || k == last_idx) ==> result[k] == '\0';
      loop assigns i, result[0..len-1];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (i == first_idx || i == last_idx) {
            result[i] = '\0'; // Mark as removed
        } else {
            result[i] = s[i];
        }
    }
}
