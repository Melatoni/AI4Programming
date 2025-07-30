// Task ID: 27
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as we are dealing with strings (char*).
*/

/*@
  // Rule II.1: Recursive logic for complexity. Not directly applicable for this problem,
  // as the logic is character-by-character.

  // Rule II.2: Helper axioms. Not directly applicable here.

  // Rule II.3: Ensures clause for boolean-like functions. Not applicable as we are modifying in-place.

  // Rule II.5: Prevent Runtime Errors (RTE).
  // Max string length to prevent potential overflow if string is excessively long.
  // Although not strictly an arithmetic overflow, it helps manage memory bounds.
  // Assuming a reasonable max string length for practical purposes.
  // A string of length 2000000000 would cause an overflow on 32-bit systems for strlen.
  // Limiting length to prevent this.
  #define MAX_STRING_LENGTH 1000000
*/

/*@
  // Axiomatic definition for is_digit
  axiomatic IsDigit {
    logic boolean is_digit_char(char c);

    // Axiom: A character is a digit if it's between '0' and '9' inclusive.
    axiom is_digit_char_def:
      \forall char c; is_digit_char(c) <==> ('0' <= c <= '9');
  }
*/

/*@
  requires \valid_read(s);
  requires \valid(s + (0 .. \strlen(s)));
  requires \strlen(s) < MAX_STRING_LENGTH; // Prevent strlen overflow

  // The function modifies the string in-place.
  assigns s[0 .. \strlen(s)];

  // Ensures that all characters in the modified string are not digits.
  // And that the length of the new string is less than or equal to the original length.
  // And that the characters not removed are preserved in order.
  ensures \forall integer k; 0 <= k < \strlen(s)@post ==> !is_digit_char(s[k]@post);
  ensures \strlen(s)@post <= \strlen(s);
  ensures \forall integer i, j;
    0 <= i < j < \strlen(s) && !is_digit_char(s[i]) && !is_digit_char(s[j]) ==>
    (\exists integer p, q;
      0 <= p < q < \strlen(s)@post && s[p]@post == s[i] && s[q]@post == s[j]
    );

  // Ensures that the characters in the resulting string are exactly those non-digit characters
  // from the original string, in their original relative order.
  ensures \forall integer k; 0 <= k < \strlen(s)@post ==>
    (\exists integer l; 0 <= l < \strlen(s) && !is_digit_char(s[l]) &&
      // s[k]@post is the k-th non-digit character from original s
      (\numof(integer m; 0 <= m < l && !is_digit_char(s[m])) == k) &&
      s[k]@post == s[l]
    );
*/
void remove_digits_from_string(char *s) {
    int read_idx = 0;
    int write_idx = 0;
    int len = 0;

    /*@
      loop invariant 0 <= len <= MAX_STRING_LENGTH;
      loop invariant \valid_read(s + (0 .. len));
      loop invariant s[len] == '\0';
      loop assigns len;
      loop variant MAX_STRING_LENGTH - len; // Assuming string length is bounded
    */
    while (s[len] != '\0') {
        len++;
    }

    /*@
      loop invariant 0 <= read_idx <= len;
      loop invariant 0 <= write_idx <= read_idx;
      loop invariant \valid_read(s + (read_idx .. len));
      loop invariant \valid(s + (write_idx .. len));

      // Characters processed so far (up to read_idx)
      loop invariant \forall integer k; 0 <= k < write_idx ==> !is_digit_char(s[k]);

      // All non-digit characters from original s[0...read_idx-1] are now in s[0...write_idx-1]
      loop invariant \forall integer k; 0 <= k < write_idx ==>
        (\exists integer l; 0 <= l < read_idx && !is_digit_char(s[l]) &&
          (\numof(integer m; 0 <= m < l && !is_digit_char(s[m])) == k) &&
          s[k] == s[l]
        );

      loop assigns read_idx, write_idx, s[0 .. len];
      loop variant len - read_idx;
    */
    while (read_idx < len) {
        /*@
          assert \valid_read(&s[read_idx]);
          assert \valid(&s[write_idx]);
        */
        if (!is_digit_char(s[read_idx])) {
            s[write_idx] = s[read_idx];
            write_idx++;
        }
        read_idx++;
    }
    s[write_idx] = '\0'; // Null-terminate the new string
}
