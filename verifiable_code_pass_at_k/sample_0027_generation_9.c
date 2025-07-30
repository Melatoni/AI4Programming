// Task ID: 27
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as we're processing characters.
  // Rule II.1, II.2: Recursive logic and helper axioms - not directly applicable for this problem's complexity.
  // Rule II.3: Ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@ axiomatic CharPredicates {
  // Rule II.1: Define a logic function for digit check.
  logic boolean is_digit(char c);

  axiom is_digit_def:
    \forall char c; is_digit(c) <==> ('0' <= c && c <= '9');
}
*/

/*@
  requires \valid(s + (0..len-1));
  requires \valid(res + (0..len-1));
  requires len >= 0;
  // Rule II.5: Ensure no overflow for index access.
  requires len < 2147483647; // Max int value - 1, to be safe.

  assigns res[0..len-1];

  // Rule II.3: Ensures clause using logical equivalence for the result of the function.
  // The function effectively "returns" the length of the new string in 'res_len',
  // and the content of 'res'.
  ensures \forall integer i; 0 <= i < \old(res_len) ==> !is_digit(res[i]);
  ensures \forall integer i; 0 <= i < \old(res_len) ==>
    \exists integer j; 0 <= j < len && !is_digit(s[j]) &&
    // This part is complex: it states that res[i] is the j-th non-digit character from s.
    // We need to count non-digits in s up to j to match the index in res.
    (\numof(integer k; 0 <= k <= j && !is_digit(s[k])) -1) == i &&
    res[i] == s[j];
  ensures \old(res_len) == \numof(integer i; 0 <= i < len && !is_digit(s[i]));
  ensures \forall integer i; \old(res_len) <= i < len ==> res[i] == '\0'; // Pad with nulls if res is larger.
*/
void remove_digits_from_string(char s[], int len, char res[], /*@ out @*/ int *res_len) {
    int k = 0; // Index for the result string

    /*@
      loop invariant 0 <= i <= len;
      loop invariant 0 <= k <= i;
      loop invariant \forall integer j; 0 <= j < k ==> !is_digit(res[j]);
      loop invariant \forall integer j; 0 <= j < k ==>
        \exists integer m; 0 <= m < i && !is_digit(s[m]) &&
        (\numof(integer p; 0 <= p <= m && !is_digit(s[p])) -1) == j &&
        res[j] == s[m];
      loop invariant k == \numof(integer j; 0 <= j < i && !is_digit(s[j]));
      loop assigns i, k, res[0..len-1];
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        if (!is_digit(s[i])) {
            res[k] = s[i];
            k++;
        }
    }

    // Null-terminate the result string (or fill remaining with nulls if res buffer is larger than needed)
    /*@
      loop invariant k <= i <= len;
      loop invariant \forall integer j; k <= j < i ==> res[j] == '\0';
      loop assigns i, res[0..len-1];
      loop variant len - i;
    */
    for (int i = k; i < len; i++) {
        res[i] = '\0';
    }

    *res_len = k;
}

/*@
  requires \valid(strings + (0..num_strings-1));
  requires \valid(strings[0].ptr + (0..strings[0].len-1)); // Example, actual requires needs to be for all strings.
  // For simplicity, assume each char_array has a valid pointer and length.
  // A more robust requires would iterate over num_strings and check each element.
  requires \forall integer i; 0 <= i < num_strings ==> \valid(strings[i].ptr + (0..strings[i].len-1));
  requires \forall integer i; 0 <= i < num_strings ==> strings[i].len >= 0;
  requires \forall integer i; 0 <= i < num_strings ==> strings[i].len < 2147483647; // Max int value - 1.

  requires \valid(output_strings + (0..num_strings-1));
  requires \forall integer i; 0 <= i < num_strings ==> \valid(output_strings[i].ptr + (0..strings[i].len-1));

  assigns output_strings[0..num_strings-1];
  assigns \forall integer i; 0 <= i < num_strings ==> output_strings[i].ptr[0..strings[i].len-1];
  assigns \forall integer i; 0 <= i < num_strings ==> output_strings[i].len;

  // The ensures clause for the main function is tricky as it's a loop over strings.
  // It effectively states that for each string, remove_digits_from_string was called correctly.
  ensures \forall integer i; 0 <= i < num_strings ==>
    (\forall integer k; 0 <= k < output_strings[i].len ==> !is_digit(output_strings[i].ptr[k]));
  ensures \forall integer i; 0 <= i < num_strings ==>
    (\forall integer k; 0 <= k < output_strings[i].len ==>
      \exists integer j; 0 <= j < strings[i].len && !is_digit(strings[i].ptr[j]) &&
      (\numof(integer p; 0 <= p <= j && !is_digit(strings[i].ptr[p])) -1) == k &&
      output_strings[i].ptr[k] == strings[i].ptr[j]);
  ensures \forall integer i; 0 <= i < num_strings ==>
    output_strings[i].len == \numof(integer j; 0 <= j < strings[i].len && !is_digit(strings[i].ptr[j]));
  ensures \forall integer i; 0 <= i < num_strings ==>
    (\forall integer k; output_strings[i].len <= k < strings[i].len ==> output_strings[i].ptr[k] == '\0');
*/
// Define a struct to represent a string with its length, similar to Python's string behavior.
struct char_array {
    char *ptr;
    int len;
};

void remove_digits_from_list_of_strings(
    struct char_array strings[], int num_strings,
    struct char_array output_strings[]
) {
    /*@
      loop invariant 0 <= i <= num_strings;
      loop invariant \forall integer j; 0 <= j < i ==>
        (\forall integer k; 0 <= k < output_strings[j].len ==> !is_digit(output_strings[j].ptr[k]));
      loop invariant \forall integer j; 0 <= j < i ==>
        (\forall integer k; 0 <= k < output_strings[j].len ==>
          \exists integer m; 0 <= m < strings[j].len && !is_digit(strings[j].ptr[m]) &&
          (\numof(integer p; 0 <= p <= m && !is_digit(strings[j].ptr[p])) -1) == k &&
          output_strings[j].ptr[k] == strings[j].ptr[m]);
      loop invariant \forall integer j; 0 <= j < i ==>
        output_strings[j].len == \numof(integer k; 0 <= k < strings[j].len && !is_digit(strings[j].ptr[k]));
      loop invariant \forall integer j; 0 <= j < i ==>
        (\forall integer k; output_strings[j].len <= k < strings[j].len ==> output_strings[j].ptr[k] == '\0');
      loop assigns i, output_strings[0..num_strings-1];
      loop assigns \forall integer j; 0 <= j < num_strings ==> output_strings[j].ptr[0..strings[j].len-1];
      loop variant num_strings - i;
    */
    for (int i = 0; i < num_strings; i++) {
        // Ensure the output string has enough space, by using the original string's length.
        // It's assumed output_strings[i].ptr points to a buffer of at least strings[i].len size.
        remove_digits_from_string(strings[i].ptr, strings[i].len,
                                  output_strings[i].ptr, &output_strings[i].len);
    }
}
