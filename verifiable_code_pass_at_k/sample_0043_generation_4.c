// Task ID: 43
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled by Frama-C.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms are crucial for prover.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  // Axiomatic block to define properties of characters.
  axiomatic CharProperties {
    logic boolean is_lowercase(char c) = (c >= 'a' && c <= 'z');
    logic boolean is_underscore(char c) = (c == '_');
  }
*/

/*@
  // Axiomatic block for recursive logic to define a "sequence"
  // A sequence is defined as 'a' or 'a_a' or 'a_a_a' etc.
  // where 'a' is a lowercase letter.
  axiomatic RegexSequence {
    // A sequence of length 1 is a lowercase letter.
    logic boolean is_regex_sequence_rec(char *s, int len);

    axiom is_regex_sequence_base:
      \forall char *s, int len;
        len == 1 && is_lowercase(s[0]) ==> is_regex_sequence_rec(s, len);

    // A sequence of length > 1 is a lowercase letter, followed by '_',
    // followed by another lowercase letter, followed by a sequence.
    axiom is_regex_sequence_recursive:
      \forall char *s, int len;
        len > 1 && len % 2 == 1 && // Length must be odd for a_a_a...
        is_lowercase(s[0]) &&
        is_underscore(s[1]) &&
        is_lowercase(s[2]) &&
        is_regex_sequence_rec(s + 2, len - 2) ==> is_regex_sequence_rec(s, len);

    // Helper axiom: If a sequence is found, all characters must be lowercase or underscore at correct positions.
    axiom is_regex_sequence_chars:
      \forall char *s, int len;
        is_regex_sequence_rec(s, len) ==>
          \forall integer i; 0 <= i < len ==>
            (i % 2 == 0 ? is_lowercase(s[i]) : is_underscore(s[i]));

    // Helper axiom: The length must be odd.
    axiom is_regex_sequence_odd_length:
      \forall char *s, int len;
        is_regex_sequence_rec(s, len) ==> (len % 2 == 1);
  }
*/

/*@
  requires \valid_read_string(str);
  // Max string length to prevent overflow with `i + len` in loop,
  // assuming a reasonable `len` up to `INT_MAX`.
  // This is a generic safeguard, specific limits might be needed based on usage.
  requires \strlen(str) <= INT_MAX - 100; // Allow some buffer

  assigns \nothing;

  // Rule II.3: Use <==> for boolean-like functions.
  // The function returns 1 if such a sequence exists, 0 otherwise.
  ensures (\exists integer i, integer len;
            0 <= i < \strlen(str) &&
            0 < len &&
            i + len <= \strlen(str) &&
            is_regex_sequence_rec(str + i, len)
          ) <==> (\result == 1);
*/
int find_regex_sequence(char *str) {
    int i = 0;
    int len = 0;
    int str_len = 0;

    /*@
      loop invariant 0 <= i <= str_len;
      loop invariant \valid_read_string(str);
      loop assigns str_len;
      loop variant \strlen(str) - i; // This is not correct for loop below
    */
    // Calculate string length manually to avoid library call
    // This loop is for calculating string length
    /*@
      loop invariant 0 <= i <= \strlen(str);
      loop invariant \valid_read_string(str);
      loop invariant \forall integer k; 0 <= k < i ==> str[k] != '\0';
      loop assigns i, str_len;
      loop variant \strlen(str) - i;
    */
    while (str[i] != '\0') {
        i++;
    }
    str_len = i;

    /*@
      loop invariant 0 <= i <= str_len;
      loop invariant \forall integer k; 0 <= k < i ==>
        !(\exists integer l; 0 < l && k + l <= str_len && is_regex_sequence_rec(str + k, l));
      loop assigns i, len;
      loop variant str_len - i;
    */
    for (i = 0; i < str_len; i++) {
        /*@
          loop invariant 0 <= len <= str_len - i;
          loop invariant \forall integer k; 0 < k < len ==>
            !is_regex_sequence_rec(str + i, k);
          loop assigns len;
          loop variant (str_len - i) - len;
        */
        for (len = 1; i + len <= str_len; len++) {
            // A sequence must have an odd length (a, a_a, a_a_a...)
            if (len % 2 == 0) {
                continue; // Rule I.2: Use int for booleans.
            }

            // Check if the current substring str[i...i+len-1] is a regex sequence
            int is_seq = 1; // Assume true
            /*@
              loop invariant 0 <= k <= len;
              loop invariant is_seq == 1 ==> \forall integer m; 0 <= m < k ==>
                (m % 2 == 0 ? (str[i+m] >= 'a' && str[i+m] <= 'z') : (str[i+m] == '_'));
              loop assigns is_seq;
              loop variant len - k;
            */
            for (int k = 0; k < len; k++) {
                if (k % 2 == 0) { // Should be a lowercase letter
                    if (!(str[i + k] >= 'a' && str[i + k] <= 'z')) {
                        is_seq = 0;
                        break;
                    }
                } else { // Should be an underscore
                    if (!(str[i + k] == '_')) {
                        is_seq = 0;
                        break;
                    }
                }
            }

            if (is_seq == 1) {
                // Found a sequence
                return 1;
            }
        }
    }

    // No sequence found
    return 0;
}
