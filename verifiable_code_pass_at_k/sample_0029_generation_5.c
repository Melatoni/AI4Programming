// Task ID: 29
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // We need to count occurrences of a number in an array.
  // This cannot be done directly with \sum or \count for WP.
  // We define a recursive logic function `count_occurrences`.
  axiomatic CountOccurrences {
    logic integer count_occurrences{L}(int* arr, integer from, integer to, int val);

    // Base case: empty range
    axiom count_occurrences_empty{L}:
      orall int* arr, integer from, integer to, int val;
        from > to ==> count_occurrences(arr, from, to, val) == 0;

    // Recursive case: If the first element matches, add 1 and recurse on the rest.
    axiom count_occurrences_match{L}:
      orall int* arr, integer from, integer to, int val;
        from <= to && arr[from] == val ==>
          count_occurrences(arr, from, to, val) == 1 + count_occurrences(arr, from + 1, to, val);

    // Recursive case: If the first element doesn't match, recurse on the rest.
    axiom count_occurrences_no_match{L}:
      orall int* arr, integer from, integer to, int val;
        from <= to && arr[from] != val ==>
          count_occurrences(arr, from, to, val) == count_occurrences(arr, from + 1, to, val);
  }
*/

/*@
  // Rule II.5: Preconditions to prevent runtime errors.
  // n must be positive for valid array indexing.
  // n must be odd, as per problem description (there's always one such element).
  requires n > 0;
  requires n % 2 == 1; // Array size must be odd for a unique odd-occurrence element.

  // The array elements must be within int range.
  requires orall integer k; 0 <= k < n ==> -2147483648 <= arr[k] <= 2147483647;

  assigns 
othing;

  // Rule II.3: Ensures clause for boolean-like functions (though this returns an int value).
  // The result is the element `x` such that its count of occurrences in `arr` is odd.
  ensures orall integer k; 0 <= k < n ==>
            (count_occurrences(arr, 0, n - 1, arr[k]) % 2 == 1) <==> (esult == arr[k]);
  // And that such an element exists and is unique (implied by problem statement for odd n).
  ensures orall integer x;
            (count_occurrences(arr, 0, n - 1, x) % 2 == 1) ==>
            (\exists integer k; 0 <= k < n && arr[k] == x && esult == x);
*/
int find_odd_occurrence(int* arr, int n) {
    int result = 0;
    /*@
      loop invariant 0 <= i <= n;
      // The XOR sum of elements processed so far (arr[0]...arr[i-1]) is stored in result.
      // Elements that appear an even number of times in arr[0]...arr[i-1] cancel out.
      // Elements that appear an odd number of times in arr[0]...arr[i-1] contribute to result.
      loop invariant orall integer x;
        (count_occurrences(arr, 0, i - 1, x) % 2 == 1) <==> ((result ^ x) < x || (result ^ x) > x); // A bit tricky to phrase XOR sum directly.
        // A simpler, more direct invariant for XOR sum:
      loop invariant result == (\xor integer k; 0 <= k < i; arr[k]);

      loop assigns i, result;
      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // XORing a number with itself results in 0.
        // If a number appears an even number of times, it cancels itself out.
        // If a number appears an odd number of times, it remains in the result.
        result = result ^ arr[i];
    }
    return result;
}
