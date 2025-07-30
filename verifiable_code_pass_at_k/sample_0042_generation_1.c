// Task ID: 42
// Generation: 1

int` elements (e.g., 0 to 1000) to make the frequency array approach viable. If elements can be arbitrary `int` values, a hash map would be needed, which is beyond the scope of simple Frama-C verification without complex axiomatic models for hash tables.

Let's assume elements are non-negative and within a fixed maximum value `MAX_VAL`.

/*@
  // Rule I.1: No standard libraries.
  // Rule II.2: Recursive logic for complexity - defines a function to count occurrences.
  // This axiomatic block defines `count_occurrences` to be used in the `sum_repeated_elements` function's ensures clause.
  axiomatic CountOccurrences {
    logic integer count_occurrences{L}(int* arr, integer from, integer to, int val) reads arr[from..to];

    // Base case: empty range
    axiom count_occurrences_empty{L}:
      \forall int* arr, integer from, integer to, int val;
        from > to ==> count_occurrences(arr, from, to, val) == 0;

    // Recursive case: value found at 'from'
    axiom count_occurrences_found{L}:
      \forall int* arr, integer from, integer to, int val;
        from <= to && arr[from] == val ==> count_occurrences(arr, from, to, val) == 1 + count_occurrences(arr, from + 1, to, val);

    // Recursive case: value not found at 'from'
    axiom count_occurrences_not_found{L}:
      \forall int* arr, integer from, integer to, int val;
        from <= to && arr[from] != val ==> count_occurrences(arr, from, to, val) == count_occurrences(arr, from + 1, to, val);

    // Rule II.2 & II.5: Helper axiom for sum of counts.
    // If an element appears multiple times, its count contributes to the sum.
    // This helps in reasoning about the total sum of repeated elements.
    axiom count__sum_helper{L}:
      \forall int* arr, integer from, integer to, int val, int k;
        count_occurrences(arr, from, to, val) >= k ==> (\exists integer i; from <= i <= to && arr[i] == val);
  }
*/

// Define a maximum value for elements to use a frequency array.
// This is a practical constraint for array-based frequency counting in C.
// Rule II.5: Prevents runtime errors related to array indexing and potential overflow of counts.
#define MAX_ELEM_VALUE 1000

/*@
  requires n >= 0;
  // Rule II.5: Precondition for frequency array size.
  // Ensure that all elements are within the bounds of MAX_ELEM_VALUE.
  requires \forall integer i; 0 <= i < n ==> 0 <= arr[i] <= MAX_ELEM_VALUE;

  assigns \nothing; // The function only reads the array and temporary state.

  // Rule II.3: Ensures clause for boolean-like functions (though this returns an int sum,
  // the principle of defining the result precisely applies).
  // The result is the sum of all elements `arr[k]` where `arr[k]` appears at least twice in the array.
  // We sum each occurrence of such repeated elements.
  ensures \result == (\sum integer k; 0 <= k < n && count_occurrences(arr, 0, n - 1, arr[k]) >= 2; arr[k]);
*/
int sum_repeated_elements(int* arr, int n) {
    // Rule I.1: No standard libraries.
    // Rule I.2: Use int for booleans. (Not directly applicable here as no booleans returned)

    // Frequency array: freq[value] stores the count of 'value' in arr.
    // Rule II.5: Prevent potential overflow if MAX_ELEM_VALUE is too large and freq array uses too much stack.
    // Assuming MAX_ELEM_VALUE is small enough for stack allocation.
    int freq[MAX_ELEM_VALUE + 1];

    // Initialize frequency array to all zeros.
    /*@
      loop invariant 0 <= i <= MAX_ELEM_VALUE + 1;
      loop invariant \forall integer k; 0 <= k < i ==> freq[k] == 0;
      loop assigns i, freq[0..MAX_ELEM_VALUE];
      loop variant MAX_ELEM_VALUE + 1 - i;
    */
    for (int i = 0; i <= MAX_ELEM_VALUE; i++) {
        freq[i] = 0;
    }

    // Populate frequency array.
    /*@
      loop invariant 0 <= i <= n;
      // After each iteration `i`, `freq[val]` contains the count of `val` in `arr[0..i-1]`.
      loop invariant \forall integer val; 0 <= val <= MAX_ELEM_VALUE ==> freq[val] == count_occurrences(arr, 0, i - 1, val);
      loop assigns i, freq[0..MAX_ELEM_VALUE];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // Rule II.5: Precondition ensures arr[i] is within bounds.
        // Rule II.5: Check for potential overflow if counts become very large.
        // Assuming n is not so large that freq[arr[i]] overflows int.
        freq[arr[i]]++;
    }

    int sum = 0;

    // Calculate the sum of repeated elements.
    /*@
      loop invariant 0 <= i <= n;
      // The sum accumulates elements that have been processed so far and are repeated.
      loop invariant sum == (\sum integer k; 0 <= k < i && count_occurrences(arr, 0, n - 1, arr[k]) >= 2; arr[k]);
      loop assigns i, sum;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // Check if the current element arr[i] is repeated (i.e., its count is >= 2)
        // Rule II.5: Precondition ensures arr[i] is within bounds.
        if (freq[arr[i]] >= 2) {
            // Rule II.5: Check for potential overflow of 'sum'.
            // Requires sum + arr[i] <= INT_MAX (or similar for the target int type).
            // This would be a 'requires' clause on the function if `n` and `MAX_ELEM_VALUE` were large.
            sum += arr[i];
        }
    }

    return sum;
}
