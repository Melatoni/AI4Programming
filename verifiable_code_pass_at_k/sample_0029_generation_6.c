// Task ID: 29
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for Booleans.
  // Rule I.3: Array pointer decay handled by Frama-C/ACSL.

  // Rule II.1: Recursive logic for complexity (if needed).
  // Rule II.2: Helper axioms (if needed).
  // Rule II.3: ensures clause for Boolean-like functions using <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.

  axiomatic XorProperties {
    logic integer xor_segment(int *a, integer start, integer end);

    axiom xor_segment_base:
      \forall int *a, integer start; xor_segment(a, start, start) == a[start];

    axiom xor_segment_recursive:
      \forall int *a, integer start, integer end;
      start < end ==> xor_segment(a, start, end) == (xor_segment(a, start, end - 1) ^ a[end]);
  }

  requires 0 <= size;
  // Rule II.5: Prevent RTE for array access.
  requires \valid_range(arr, 0, size - 1);

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The element occurring an odd number of times is the XOR sum of all elements.
  ensures \result == xor_segment(arr, 0, size - 1);
*/
int find_odd_occurrence(int *arr, int size) {
    int result = 0;

    /*@
      loop invariant 0 <= i <= size;
      // The current result is the XOR sum of elements from arr[0] to arr[i-1].
      loop invariant result == xor_segment(arr, 0, i - 1);
      loop assigns i, result;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        result ^= arr[i];
    }
    return result;
}
