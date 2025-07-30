// Task ID: 18
// Generation: 4

/*@
  // Axiomatic block for character presence in a string.
  axiomatic CharPresence {
    logic boolean char_is_present(char c, char* s, integer len) reads s[0..len-1];

    // Base case: empty string
    axiom char_is_present_empty{
      \forall char c, char* s;
        char_is_present(c, s, 0) == \false;
    }

    // Recursive case: check first char, then rest of string
    axiom char_is_present_recursive{
      \forall char c, char* s, integer len;
        len > 0 ==> (char_is_present(c, s, len) <==> (s[0] == c || char_is_present(c, s + 1, len - 1)));
    }
  }
*/

/*@
  requires \valid(str1 + (0..len1-1));
  requires \valid(str2 + (0..len2-1));
  requires len1 >= 0;
  requires len2 >= 0;
  requires \separated(str1 + (0..len1-1), str2 + (0..len2-1));

  // The function modifies str1 in place.
  assigns str1[0..len1-1];

  // The function returns the new length of str1.
  ensures \result >= 0 && \result <= len1;
  ensures \forall integer i; 0 <= i < \result ==>
    !char_is_present(str1[i], str2, len2);
  ensures \forall integer i; 0 <= i < len1 ==>
    (char_is_present(str1[i], str2, len2) ==>
     \forall integer j; 0 <= j < \result ==> str1[j] != \old(str1[i]));
  ensures \forall integer i, j; 0 <= i < \result && 0 <= j < len1 && \old(str1[j]) == str1[i] ==>
    !char_is_present(\old(str1[j]), str2, len2);
  ensures \forall integer i, j; 0 <= i < \result && 0 <= j < len1 && \old(str1[j]) == str1[i] ==>
    \exists integer k; 0 <= k < len1 && \old(str1[k]) == str1[i] && !char_is_present(\old(str1[k]), str2, len2);
  ensures \forall integer i; 0 <= i < \result ==>
    \exists integer j; 0 <= j < len1 && str1[i] == \old(str1[j]) && !char_is_present(\old(str1[j]), str2, len2);
*/
int remove_chars(char* str1, int len1, char* str2, int len2) {
    int write_idx = 0;
    /*@
      loop invariant 0 <= write_idx <= read_idx;
      loop invariant read_idx <= len1;
      loop invariant \forall integer k; 0 <= k < write_idx ==>
        !char_is_present(str1[k], str2, len2);
      loop invariant \forall integer k; write_idx <= k < read_idx ==>
        char_is_present(\at(str1[k], Pre), str2, len2);
      loop invariant \forall integer k; 0 <= k < write_idx ==>
        \exists integer j; 0 <= j < read_idx && str1[k] == \at(str1[j], Pre) && !char_is_present(\at(str1[j], Pre), str2, len2);
      loop invariant \forall integer k; 0 <= k < write_idx ==>
        \forall integer p; write_idx <= p < read_idx ==> str1[k] != str1[p];

      loop assigns write_idx, str1[0..len1-1], read_idx;
      loop variant len1 - read_idx;
    */
    for (int read_idx = 0; read_idx < len1; read_idx++) {
        /*@
          // Assertion to help the prover understand the char_is_present logic.
          // This ensures the loop body's condition is well-formed with respect to the `char_is_present` logic.
          assert char_is_present(str1[read_idx], str2, len2) == (\exists integer k; 0 <= k < len2 && str1[read_idx] == str2[k]);
        */
        int char_found_in_str2 = 0; // Use int for boolean
        /*@
          loop invariant 0 <= k <= len2;
          loop invariant char_found_in_str2 == 0 ==> \forall integer p; 0 <= p < k ==> str1[read_idx] != str2[p];
          loop invariant char_found_in_str2 == 1 ==> \exists integer p; 0 <= p < k && str1[read_idx] == str2[p];
          loop assigns char_found_in_str2, k;
          loop variant len2 - k;
        */
        for (int k = 0; k < len2; k++) {
            if (str1[read_idx] == str2[k]) {
                char_found_in_str2 = 1;
                break;
            }
        }

        if (char_found_in_str2 == 0) {
            // Character is not in str2, keep it
            str1[write_idx] = str1[read_idx];
            write_idx++;
        }
    }
    return write_idx;
}
