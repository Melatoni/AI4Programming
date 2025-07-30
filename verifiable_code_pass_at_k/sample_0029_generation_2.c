// Task ID: 29
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Define recursive logic for complex properties.
  axiomatic OddCount {
    logic integer count_occurrences(int* a, int size, int val);

    axiom count_occurrences_base:
      \forall int* a, int val;
        count_occurrences(a, 0, val) == 0;

    axiom count_occurrences_recursive:
      \forall int* a, int size, int val;
        size > 0 ==> count_occurrences(a, size, val) ==
          (if a[size - 1] == val then 1 else 0) + count_occurrences(a, size - 1, val);

    // Rule II.2: Helper axioms for properties.
    // Proves that if a value appears an odd number of times, its count is not even.
    axiom count_occurrences_odd_is_not_even:
      \forall int* a, int size, int val;
        count_occurrences(a, size, val) % 2 == 1 ==> count_occurrences(a, size, val) % 2 != 0;

    // Proves that if a value appears an even number of times, its count is not odd.
    axiom count_occurrences_even_is_not_odd:
      \forall int* a, int size, int val;
        count_occurrences(a, size, val) % 2 == 0 ==> count_occurrences(a, size, val) % 2 != 1;
  }
*/

/*@
  requires size >= 0;
  requires \valid_read_range(a, 0, size - 1);

  // Rule II.5: Prevent runtime errors. No specific overflow for this logic, but good practice.
  // The problem implies that such an element exists. We ensure it.
  requires \exists integer k; 0 <= k < size && count_occurrences(a, size, a[k]) % 2 == 1;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like functions.
  ensures 0 <= \result < size && count_occurrences(a, size, a[\result]) % 2 == 1;
*/
int find_odd_occurrence(int* a, int size) {
    int result = 0;
    /*@
      loop invariant 0 <= i <= size;
      // The invariant captures the property of XOR:
      // result contains the XOR sum of elements processed so far.
      // If an element appears an even number of times, it cancels out.
      // If an element appears an odd number of times, it remains.
      loop invariant result == (\xor integer k; 0 <= k < i; a[k]);
      loop assigns result, i;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        result = result ^ a[i];
    }
    // The problem statement implies such an element exists and is unique.
    // The XOR property ensures that the final 'result' is that element.
    return result;
}
