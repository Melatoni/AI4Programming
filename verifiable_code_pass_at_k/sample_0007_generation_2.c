// Task ID: 7
// Generation: 2

char` array up to a given length `n`) contains a sequence of at least `MIN_LEN` (where `MIN_LEN` is 4) identical characters.

/*@
    // Rule I.1: No standard libraries. Define constants directly.
    #define MIN_LEN 4

    // Rule II.1, II.2: Define a recursive logic function to check for repeating characters.
    // This axiomatic block defines properties about sequences of identical characters.
    axiomatic IdenticalCharSequence {
        // is_identical_char_sequence(s, start, end, c) is true if s[start..end-1]
        // consists only of character c.
        logic boolean is_identical_char_sequence{L}(char *s, int start, int end, char c)
            reads s[0..end-1];

        // Base case: An empty sequence is not an identical char sequence of length > 0.
        axiom is_identical_char_sequence_empty{L}:
            \forall char *s, int start, char c;
                is_identical_char_sequence(s, start, start, c) == \true; // An empty sequence is trivially "identical"

        // Recursive case: A sequence is identical if its first char matches and the rest of the sequence is identical.
        axiom is_identical_char_sequence_recursive{L}:
            \forall char *s, int start, int end, char c;
                start < end ==>
                (is_identical_char_sequence(s, start, end, c) <==>
                 (s[start] == c && is_identical_char_sequence(s, start + 1, end, c)));

        // Rule II.2: Helper axiom - if a sequence is identical, all its characters are the same as the first.
        axiom is_identical_char_sequence_all_same{L}:
            \forall char *s, int start, int end, char c;
                is_identical_char_sequence(s, start, end, c) ==>
                (\forall integer k; start <= k < end ==> s[k] == c);

        // Helper axiom: if a sequence is identical to one character, it's identical to that character only.
        axiom is_identical_char_sequence_unique_char{L}:
            \forall char *s, int start, int end, char c1, char c2;
                is_identical_char_sequence(s, start, end, c1) && start < end && c1 != c2 ==>
                !is_identical_char_sequence(s, start, end, c2);
    }
*/

/*@
    requires n >= 0; // String length can be 0.
    requires \valid_read_range(s, 0, n - 1); // s must be readable up to n-1.

    assigns \nothing; // Function does not modify memory.

    // Rule II.3: Ensures clause uses logical equivalence.
    // The function returns 1 if there exists a substring of MIN_LEN identical characters.
    ensures (\exists integer i;
                0 <= i && i <= n - MIN_LEN && // Start index i is valid.
                is_identical_char_sequence(s, i, i + MIN_LEN, s[i])) // The sequence s[i..i+MIN_LEN-1] is identical and long enough.
            <==> (\result == 1);
*/
int contains_min_len_identical_chars(char *s, int n) {
    // Rule II.5: Prevent potential out-of-bounds access if n is too small for MIN_LEN.
    if (n < MIN_LEN) {
        return 0;
    }

    /*@
        loop invariant 0 <= i <= n - MIN_LEN + 1; // i iterates up to the last possible start of a MIN_LEN sequence.
        loop invariant \forall integer k;
                            0 <= k < i ==> // For all previously checked starting positions k:
                            !(\exists char c; is_identical_char_sequence(s, k, k + MIN_LEN, c)); // No MIN_LEN identical sequence found starting at k.
        loop invariant \forall integer k; 0 <= k < n ==> \valid_read(s + k); // s remains valid.
        loop assigns i;
        loop variant (n - MIN_LEN + 1) - i; // Variant for termination.
    */
    for (int i = 0; i <= n - MIN_LEN; ++i) {
        char first_char = s[i];
        int all_same = 1; // Rule I.2: Use int for booleans.

        /*@
            loop invariant i <= j <= i + MIN_LEN; // j iterates within the current MIN_LEN window.
            loop invariant \forall integer k;
                                i <= k < j ==> s[k] == first_char; // All chars checked so far in this window are first_char.
            loop invariant all_same == (j == i || (\forall integer k; i <= k < j ==> s[k] == first_char)); // all_same reflects correctness.
            loop assigns j, all_same;
            loop variant (i + MIN_LEN) - j; // Variant for termination of inner loop.
        */
        for (int j = i + 1; j < i + MIN_LEN; ++j) {
            if (s[j] != first_char) {
                all_same = 0;
                break; // Rule for efficiency in C, logic is covered by loop invariant.
            }
        }

        if (all_same) {
            return 1; // Found a sequence of MIN_LEN identical characters.
        }
    }

    return 0; // No such sequence found.
}
