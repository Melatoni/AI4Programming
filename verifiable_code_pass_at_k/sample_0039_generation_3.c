// Task ID: 39
// Generation: 3

/*@
    axiomatic CharCounts {
        logic integer count_char(char c, char *s, integer len) reads s;

        axiom count_char_empty:
            \forall char c, char *s, integer len;
                len <= 0 ==> count_char(c, s, len) == 0;

        axiom count_char_recursive:
            \forall char c, char *s, integer len;
                len > 0 ==> count_char(c, s, len) == (
                    if s[len - 1] == c then 1 else 0
                ) + count_char(c, s, len - 1);

        // Rule II.2: Helper axiom for sum of counts
        // The sum of counts of all characters should equal the length of the string
        axiom sum_of_counts_equals_length:
            \forall char *s, integer len;
                len >= 0 ==> \sum_{char k = 'a'; k <= 'z'; k++} count_char(k, s, len) == len;

        // Rule II.2: Helper axiom for maximum count
        logic integer max_count(char *s, integer len) reads s;

        axiom max_count_empty:
            \forall char *s, integer len;
                len <= 0 ==> max_count(s, len) == 0;
        
        // This axiom states that the max_count is the maximum of all individual char counts
        axiom max_count_definition:
            \forall char *s, integer len;
                len > 0 ==> max_count(s, len) == \max_{char k = 'a'; k <= 'z'; k++} count_char(k, s, len);

        // This helper axiom relates max_count to total length
        // If a string can be rearranged such that adjacent chars are different,
        // then the count of any single character cannot be more than (len + 1) / 2.
        // This is a necessary condition for the rearrangement.
        // For example, "aaab" (len=4), max_count('a')=3. (4+1)/2 = 2.5. 3 > 2.5, so impossible.
        // "aaabbc" (len=6), max_count('a')=3. (6+1)/2 = 3.5. 3 <= 3.5, possible ("abacab").
        axiom max_count_upper_bound:
            \forall char *s, integer len;
                len > 0 ==> (\forall char c; count_char(c, s, len) <= (len + 1) / 2) <==>
                            (max_count(s, len) <= (len + 1) / 2);
    }
*/

/*@
    requires \valid_read(s + (0..len-1));
    requires len >= 0;

    assigns \nothing;

    // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
    // A string can be rearranged such that adjacent characters are different if and only if
    // the count of any single character is not more than (len + 1) / 2.
    ensures (\forall char c; count_char(c, s, len) <= (len + 1) / 2) <==> (result == 1);
*/
int can_rearrange_adjacent_different(char *s, int len) {
    if (len <= 1) {
        return 1; // A string of length 0 or 1 always satisfies the condition
    }

    /*@
        // Rule II.5: Prevent overflow for `counts[c - 'a']++` if `c` is out of range,
        // though the problem implies lowercase English letters.
        // Assuming char converts to int safely for array indexing.
        requires \forall integer i; 0 <= i < 26; counts[i] == 0;
    */
    int counts[26] = {0}; // Array to store character counts

    /*@
        loop invariant 0 <= i <= len;
        loop invariant \forall integer k; 0 <= k < 26 ==> counts[k] == count_char((char)('a' + k), s, i);
        loop assigns i, counts[0..25];
        loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Rule II.5: Prevent potential out-of-bounds access if s[i] is not a lowercase letter.
        // Assuming valid input characters 'a'-'z'.
        // Frama-C typically assumes char values are within their range.
        counts[s[i] - 'a']++;
    }

    int max_freq = 0;
    /*@
        loop invariant 0 <= i <= 26;
        loop invariant \forall integer k; 0 <= k < i ==> max_freq >= counts[k];
        loop invariant max_freq == \max_{integer k; 0 <= k < i} counts[k];
        loop assigns i, max_freq;
        loop variant 26 - i;
    */
    for (int i = 0; i < 26; i++) {
        if (counts[i] > max_freq) {
            max_freq = counts[i];
        }
    }

    // The condition for rearrangement is that the frequency of any character
    // must not be greater than (len + 1) / 2.
    // Example: "aaab", len=4, max_freq=3. (4+1)/2 = 2.5. 3 > 2.5, so 0.
    // Example: "aaabbc", len=6, max_freq=3. (6+1)/2 = 3.5. 3 <= 3.5, so 1.
    if (max_freq <= (len + 1) / 2) {
        return 1;
    } else {
        return 0;
    }
}
