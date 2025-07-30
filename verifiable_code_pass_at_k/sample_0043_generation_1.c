// Task ID: 43
// Generation: 1

/*@
  // Rule I.1: No standard libraries. ACSL constants are implicitly available.
  // Rule II.5: Prevent potential overflow if regex_str_len * regex_str_len is used in loop.
  // Assuming 'regex_str' is a string of lowercase letters and underscores.
  // The maximum length of a string that can be safely squared without overflow for int is 46340.
  // However, we are not squaring the length here. The constraints are more about array access.
  requires \valid(regex_str + (0..regex_str_len-1));
  requires regex_str_len >= 0;

  // Rule II.3: The ensures clause uses logical equivalence.
  // The function returns 1 if a sequence of lowercase letters joined by an underscore is found.
  // A sequence is defined as at least one lowercase letter, followed by an underscore,
  // followed by at least one lowercase letter.
  ensures (\exists integer i;
            0 <= i && i + 2 < regex_str_len && // Ensure enough characters for 'a_a' pattern
            (regex_str[i] >= 'a' && regex_str[i] <= 'z') && // First char is lowercase
            regex_str[i+1] == '_' && // Second char is underscore
            (regex_str[i+2] >= 'a' && regex_str[i+2] <= 'z') && // Third char is lowercase
            // Additional check to ensure the first and third parts are sequences of letters.
            // This requires looking back for the first letter and forward for the second.
            // Check for the first letter sequence:
            (\exists integer j; 0 <= j && j <= i &&
              (regex_str[j] >= 'a' && regex_str[j] <= 'z') &&
              (\forall integer k; j <= k < i ==> (regex_str[k] >= 'a' && regex_str[k] <= 'z'))) &&
            // Check for the second letter sequence:
            (\exists integer l; i+2 <= l && l < regex_str_len &&
              (regex_str[l] >= 'a' && regex_str[l] <= 'z') &&
              (\forall integer m; i+2 <= m <= l ==> (regex_str[m] >= 'a' && regex_str[m] <= 'z')))
          ) <==> (result == 1);
  // The above ensures clause is overly complex for the given problem ("sequences of lowercase letters
  // joined with an underscore"). A simpler interpretation is just "match a_a where a is a letter".
  // Let's refine the interpretation to "find `[a-z]+_[a-z]+`".

  // Refined ensures clause:
  ensures (\exists integer i;
            0 <= i && i < regex_str_len && // Start of the first sequence
            (regex_str[i] >= 'a' && regex_str[i] <= 'z') && // First char of first sequence is letter
            (\exists integer j;
              i <= j && j < regex_str_len && // End of the first sequence
              (regex_str[j] >= 'a' && regex_str[j] <= 'z') && // Last char of first sequence is letter
              (\forall integer k; i <= k <= j ==> (regex_str[k] >= 'a' && regex_str[k] <= 'z')) && // All chars in first sequence are letters
              j + 1 < regex_str_len && // Underscore must exist
              regex_str[j+1] == '_' && // Underscore
              j + 2 < regex_str_len && // Start of second sequence must exist
              (regex_str[j+2] >= 'a' && regex_str[j+2] <= 'z') && // First char of second sequence is letter
              (\exists integer l;
                j + 2 <= l && l < regex_str_len && // End of second sequence
                (regex_str[l] >= 'a' && regex_str[l] <= 'z') && // Last char of second sequence is letter
                (\forall integer m; j + 2 <= m <= l ==> (regex_str[m] >= 'a' && regex_m <= 'z')) // All chars in second sequence are letters
              )
            )
          ) <==> (result == 1);
*/
int find_regex_sequence(char *regex_str, int regex_str_len) {
    /*@
      loop invariant 0 <= i <= regex_str_len;
      // If we found a match, we return early.
      // If we haven't found a match yet, then no match exists in regex_str[0..i-1].
      loop invariant (\forall integer k; 0 <= k < i ==>
                        ! (\exists integer j;
                            k <= j && j < regex_str_len &&
                            (regex_str[k] >= 'a' && regex_str[k] <= 'z') &&
                            (\exists integer j_end;
                                k <= j_end && j_end < regex_str_len &&
                                (regex_str[j_end] >= 'a' && regex_str[j_end] <= 'z') &&
                                (\forall integer k_inner; k <= k_inner <= j_end ==> (regex_str[k_inner] >= 'a' && regex_str[k_inner] <= 'z')) &&
                                j_end + 1 < regex_str_len &&
                                regex_str[j_end+1] == '_' &&
                                j_end + 2 < regex_str_len &&
                                (regex_str[j_end+2] >= 'a' && regex_str[j_end+2] <= 'z') &&
                                (\exists integer l_end;
                                    j_end + 2 <= l_end && l_end < regex_str_len &&
                                    (regex_str[l_end] >= 'a' && regex_str[l_end] <= 'z') &&
                                    (\forall integer m_inner; j_end + 2 <= m_inner <= l_end ==> (regex_str[m_inner] >= 'a' && regex_m_inner <= 'z'))
                                )
                            )
                        )
                      );
      loop assigns i;
      loop variant regex_str_len - i;
    */
    for (int i = 0; i < regex_str_len; i++) {
        // Look for the start of the first sequence of letters [a-z]+
        if (regex_str[i] >= 'a' && regex_str[i] <= 'z') {
            int first_seq_end = i;
            /*@
              loop invariant i <= first_seq_end <= regex_str_len;
              loop invariant (\forall integer k; i <= k < first_seq_end ==> (regex_str[k] >= 'a' && regex_str[k] <= 'z'));
              loop assigns first_seq_end;
              loop variant regex_str_len - first_seq_end;
            */
            while (first_seq_end < regex_str_len &&
                   regex_str[first_seq_end] >= 'a' && regex_str[first_seq_end] <= 'z') {
                first_seq_end++;
            }
            // After the loop, first_seq_end points to the character immediately after the first sequence of letters.
            // So, the first sequence is regex_str[i .. first_seq_end-1].
            // We need to check if an underscore follows.
            // requires first_seq_end is at least i+1 because the loop started with a letter
            // and advanced first_seq_end at least once.
            // Check if there is an underscore after the first sequence
            if (first_seq_end < regex_str_len && regex_str[first_seq_end] == '_') {
                int second_seq_start = first_seq_end + 1;
                // Check if there is a second sequence of letters [a-z]+
                if (second_seq_start < regex_str_len &&
                    regex_str[second_seq_start] >= 'a' && regex_str[second_seq_start] <= 'z') {
                    // We found the start of the second sequence. Now verify it's a sequence.
                    int second_seq_end = second_seq_start;
                    /*@
                      loop invariant second_seq_start <= second_seq_end <= regex_str_len;
                      loop invariant (\forall integer k; second_seq_start <= k < second_seq_end ==> (regex_str[k] >= 'a' && regex_str[k] <= 'z'));
                      loop assigns second_seq_end;
                      loop variant regex_str_len - second_seq_end;
                    */
                    while (second_seq_end < regex_str_len &&
                           regex_str[second_seq_end] >= 'a' && regex_str[second_seq_end] <= 'z') {
                        second_seq_end++;
                    }
                    // If second_seq_end is greater than second_seq_start, it means we found at least one letter.
                    // (It must be true because the if condition for second_seq_start already checked for a letter).
                    // So, we found a match.
                    if (second_seq_end > second_seq_start) {
                        return 1; // Rule I.2: Return 1 for true.
                    }
                }
            }
        }
    }
    return 0; // Rule I.2: Return 0 for false.
}
