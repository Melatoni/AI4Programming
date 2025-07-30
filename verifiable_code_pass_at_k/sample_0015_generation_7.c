// Task ID: 15
// Generation: 7

/*@ axiomatic LowercaseSplit {
  @   logic int is_lowercase(char c);
  @   axiom is_lowercase_def:
  @     \forall char c; is_lowercase(c) == (c >= 'a' && c <= 'z');
  @
  @   // Rule II.2: Helper axiom for properties over sequences.
  @   // This axiom states that if a character is not lowercase, then it's not lowercase up to that point.
  @   // This helps the prover reason about the prefix of the string.
  @   axiom not_lowercase_prefix:
  @     \forall char c, integer i;
  @       !is_lowercase(c) ==> \forall integer k; 0 <= k <= i ==> !is_lowercase(c); // Simplified, not directly used for this problem, but shows the concept.
  @
  @   // A more relevant helper axiom for string splitting:
  @   // If a character at index `idx` is lowercase, then it's the first lowercase character in the string `s` up to `idx`
  @   // if all characters before it were not lowercase.
  @   axiom first_lowercase_iff:
  @     \forall char *s, integer idx;
  @       (is_lowercase(s[idx]) && (\forall integer k; 0 <= k < idx ==> !is_lowercase(s[k])))
  @       <==> (idx >= 0 && idx < \strlen(s) && is_lowercase(s[idx]) && (\forall integer k; 0 <= k < idx ==> !is_lowercase(s[k])));
  @ }
  @*/

/*@
  @ requires \valid_read(s);
  @ requires \strlen(s) >= 0; // String can be empty
  @
  @ assigns \nothing;
  @
  @ // Rule II.3: Ensures clause for boolean-like function using logical equivalence.
  @ // The function returns 1 if there exists an index `i` such that s[i] is a lowercase letter
  @ // AND all characters before s[i] are NOT lowercase.
  @ // It returns 0 otherwise, meaning either no lowercase letters exist, or a lowercase letter
  @ // exists but it's not the first occurrence (i.e., a lowercase letter appeared before it).
  @ ensures (\exists integer i;
  @            0 <= i < \strlen(s) &&
  @            is_lowercase(s[i]) &&
  @            (\forall integer k; 0 <= k < i ==> !is_lowercase(s[k]))
  @         ) <==> (result == 1);
  @*/
int split_at_lowercase(char *s) { // Rule I.2: Uses int for boolean result.
    /*@
      @ loop invariant 0 <= i <= \strlen(s);
      @ // Rule II.4: Invariant capturing that no lowercase characters have been found so far in the prefix.
      @ loop invariant \forall integer k; 0 <= k < i ==> !is_lowercase(s[k]);
      @ loop assigns i;
      @ loop variant \strlen(s) - i;
    */
    for (int i = 0; s[i] != '\0'; i++) {
        if (s[i] >= 'a' && s[i] <= 'z') {
            return 1; // Found the first lowercase character, so a split point exists.
        }
    }
    return 0; // No lowercase character found in the entire string.
}
