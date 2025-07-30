// Task ID: 18
// Generation: 1

/*@ axiomatic CharInString {
  // Rule II.1: Recursive logic for checking if a character is present in a string.
  logic int is_char_in_string(char c, char *s, int len);

  axiom is_char_in_string_empty{
    \forall char c, char *s;
    is_char_in_string(c, s, 0) == 0;
  }

  axiom is_char_in_string_rec{
    \forall char c, char *s, integer len;
    len > 0 ==>
    is_char_in_string(c, s, len) == (if s[len - 1] == c then 1 else is_char_in_string(c, s, len - 1));
  }

  // Rule II.2: Helper axiom to state that if a char is in a string, its presence doesn't change
  // if the string is extended (as long as the char is still within the considered length).
  // This is crucial for loop invariants.
  axiom is_char_in_string_helper_prefix{
    \forall char c, char *s, integer len1, integer len2;
    0 <= len1 <= len2 ==>
    (is_char_in_string(c, s, len1) == 1 ==> is_char_in_string(c, s, len2) == 1);
  }

  // Helper axiom for the opposite direction: if char is not in a prefix, it's not in that prefix.
  axiom is_char_in_string_helper_suffix{
    \forall char c, char *s, integer len1, integer len2;
    0 <= len1 <= len2 ==>
    (is_char_in_string(c, s, len2) == 0 ==> is_char_in_string(c, s, len1) == 0);
  }

}
*/

/*@
  requires \valid_read(str1 + (0..len1 - 1));
  requires \valid_read(str2 + (0..len2 - 1));
  requires len1 >= 0;
  requires len2 >= 0;
  requires \valid(str_out + (0..len1 - 1));
  requires str_out != str1; // Output buffer must be distinct from input str1
  requires str_out != str2; // Output buffer must be distinct from input str2

  assigns str_out[0..len1-1];

  // Rule II.3: Ensures clause uses logical equivalence.
  // The result (return value) is the new length of the string.
  ensures \forall integer i; 0 <= i < \result ==>
          is_char_in_string(str_out[i], str2, len2) == 0; // char is NOT in str2

  ensures \forall integer i; 0 <= i < \result ==>
          is_char_in_string(str_out[i], str1, len1) == 1; // char was originally in str1

  ensures \forall integer i; 0 <= i < len1 ==>
          (is_char_in_string(str1[i], str2, len2) == 0 <==>
           \exists integer k; 0 <= k < \result && str_out[k] == str1[i]);

  // The new length is at most the original length.
  ensures \result <= len1;
*/
int remove_chars(char *str1, int len1, char *str2, int len2, char *str_out) {
  int k = 0; // Index for the output string

  /*@
    loop invariant 0 <= i <= len1;
    loop invariant 0 <= k <= i;

    // All characters copied to str_out so far are not in str2
    loop invariant \forall integer j; 0 <= j < k ==> is_char_in_string(str_out[j], str2, len2) == 0;

    // All characters copied to str_out so far were originally in str1
    loop invariant \forall integer j; 0 <= j < k ==> is_char_in_string(str_out[j], str1, len1) == 1;

    // For any character in str1 processed so far (up to i-1), if it's not in str2,
    // it must have been copied to str_out.
    loop invariant \forall integer j; 0 <= j < i ==>
                   (is_char_in_string(str1[j], str2, len2) == 0 <==>
                    \exists integer p; 0 <= p < k && str_out[p] == str1[j]);

    loop assigns i, k, str_out[0..len1-1];
    loop variant len1 - i;
  */
  for (int i = 0; i < len1; i++) {
    // Check if str1[i] is present in str2
    /*@
      loop invariant 0 <= j <= len2;
      loop invariant \forall integer m; 0 <= m < j ==> str2[m] != str1[i];
      loop assigns j, char_found;
      loop variant len2 - j;
    */
    int char_found = 0; // Rule I.2: Use int for boolean
    for (int j = 0; j < len2; j++) {
      if (str1[i] == str2[j]) {
        char_found = 1;
        break;
      }
    }

    if (char_found == 0) { // If char1[i] is NOT in str2
      str_out[k] = str1[i];
      k++;
    }
  }

  return k;
}
