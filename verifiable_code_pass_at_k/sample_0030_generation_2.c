// Task ID: 30
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic CharCount {
    logic integer count_char_in_prefix(char_code, char_array_ptr, length, prefix_length);

    axiom count_char_in_prefix_base:
      \forall char_array_ptr s, integer length, char_code_val;
        count_char_in_prefix(char_code_val, s, length, 0) == 0;

    axiom count_char_in_prefix_recursive:
      \forall char_array_ptr s, integer length, integer prefix_len, char_code_val;
        0 <= prefix_len < length ==>
        count_char_in_prefix(char_code_val, s, length, prefix_len + 1) ==
        count_char_in_prefix(char_code_val, s, length, prefix_len) +
        (if s[prefix_len] == char_code_val then 1 else 0);

    // Helper axiom: The count cannot exceed the prefix length.
    axiom count_char_in_prefix_upper_bound:
      \forall char_array_ptr s, integer length, integer prefix_len, char_code_val;
        0 <= prefix_len <= length ==>
        count_char_in_prefix(char_code_val, s, length, prefix_len) <= prefix_len;

    // Helper axiom: The count is non-negative.
    axiom count_char_in_prefix_non_negative:
      \forall char_array_ptr s, integer length, integer prefix_len, char_code_val;
        0 <= prefix_len <= length ==>
        count_char_in_prefix(char_code_val, s, length, prefix_len) >= 0;
  }
*/

/*@
  requires \valid_read(s + (0..length-1));
  requires length >= 0;
  // Rule II.5: Prevent potential overflow for 'result' if length is very large.
  // The maximum number of substrings is length * (length + 1) / 2.
  // For int, length should be <= 65535 to avoid overflow in length*(length+1)/2,
  // but here we are summing counts, so max value for one char could be length.
  // A rough upper bound for result is length * (length+1).
  // If length is INT_MAX, length * (length+1) overflows.
  // Let's assume length is reasonably small to fit in int.
  // Max result for length=46340 would be 46340 * 46341 / 2 approx 10^9.
  // If length is ~65535, result can be ~2*10^9. This fits in int.
  // However, the sum of counts `count * (count + 1) / 2` could still overflow
  // if `count` is large. The maximum `count` for any character is `length`.
  // So, `length * (length + 1) / 2` is the max contribution from one char.
  // If length is around 65535, this is ~2*10^9.
  // If there are 256 distinct characters, the total sum could be 256 * 2*10^9, which overflows.
  // So we need a tighter bound on length if all chars contribute.
  // A safer bound for `length` to prevent `result` overflow:
  // If length <= 200, result <= 200 * 201 / 2 * 256 (max unique chars) = 20200 * 256 = 5,171,200 (fits int).
  // Let's use a conservative bound.
  requires length <= 1000; // Max result will be approx 1000^2 * 256 = 2.5 * 10^8, fits int.

  assigns \nothing;

  behavior empty_string:
    assumes length == 0;
    ensures \result == 0;

  behavior non_empty_string:
    assumes length > 0;
    // The ensures clause describes the logic: sum of nC2 for each character count
    // plus the length (for single-character substrings).
    // Sum_{c in unique_chars} (count(c) * (count(c) + 1) / 2)
    // This is equivalent to sum_{i=0..length-1} (count of s[i] up to i)
    // which is sum_{i=0..length-1} (count_char_in_prefix(s[i], s, length, i+1))
    // This is hard to represent directly in ACSL for a global sum.
    // Let's ensure the result is the correct sum of combinations for each character.

    // A simpler way: total number of substrings starting and ending with the same character
    // is the sum of (k * (k+1) / 2) for each character that appears k times.
    // This is hard to express as a single \sum in ACSL directly without iterating over characters.
    // Instead, we can ensure the result is non-negative and is the sum of (count_i * (count_i + 1) / 2)
    // where count_i is the number of occurrences of the character at index i.
    // This is the number of substrings ending at `i` and starting with `s[i]`.
    // No, this is not correct. The formula is sum over distinct characters.
    // e.g. "aaa" -> a: 3 times. 3*(3+1)/2 = 6.
    // Substrings: "a"(0,0), "a"(1,1), "a"(2,2), "aa"(0,1), "aa"(1,2), "aaa"(0,2). Total 6.

    // Let's use an existential to describe the property of the result.
    // This is equivalent to `length + sum_{i=0..length-1} (count of s[i] in s[0..i-1])`
    // This is exactly what the algorithm does.
    ensures \result == \sum(integer i; 0 <= i < length; count_char_in_prefix(s[i], s, length, i + 1));
*/
int count_substrings_same_char(char *s, int length) {
    int result = 0;
    /*@
      loop invariant 0 <= i <= length;
      loop invariant result == \sum(integer k; 0 <= k < i; count_char_in_prefix(s[k], s, length, k + 1));
      loop assigns i, result;
      loop variant length - i;
    */
    for (int i = 0; i < length; i++) {
        // For each character s[i], we need to count how many times it appeared
        // from index 0 to i (inclusive).
        // Each time s[i] appears, it contributes to new substrings ending at 'i'.
        // The count of s[i] in s[0..i] is `count_char_in_prefix(s[i], s, length, i+1)`.
        // This is exactly the number of substrings ending at 'i' that also start with s[i].
        // Example: "aba"
        // i=0, s[0]='a'. `count_char_in_prefix('a', s, 3, 1)` is 1. result = 1. ("a")
        // i=1, s[1]='b'. `count_char_in_prefix('b', s, 3, 2)` is 1. result = 1+1 = 2. ("a", "b")
        // i=2, s[2]='a'. `count_char_in_prefix('a', s, 3, 3)` is 2. result = 2+2 = 4. ("a", "b", "a", "aba")
        // This is the correct logic.

        int current_char_count_in_prefix = 0;
        /*@
          loop invariant 0 <= j <= i;
          loop invariant current_char_count_in_prefix == count_char_in_prefix(s[i], s, length, j);
          loop assigns j, current_char_count_in_prefix;
          loop variant i - j;
        */
        for (int j = 0; j <= i; j++) {
            if (s[j] == s[i]) {
                current_char_count_in_prefix++;
            }
        }
        result += current_char_count_in_prefix;
    }
    return result;
}
