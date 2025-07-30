// Task ID: 29
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in ACSL.

  // Rule II.1: Recursive logic for XOR sum.
  // Rule II.2: Helper axioms for properties.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic OddOccurrence {
    logic integer xor_sum_range(int *a, int low, int high);

    axiom xor_sum_base:
      \forall int *a, int low;
        xor_sum_range(a, low, low) == a[low];

    axiom xor_sum_recursive:
      \forall int *a, int low, int high;
        low < high ==> xor_sum_range(a, low, high) == (xor_sum_range(a, low, high - 1) ^ a[high]);

    // Helper axiom: XORing an even number of times with itself results in 0.
    // XORing an odd number of times with itself results in the number itself.
    // This axiom helps the prover understand the property of XOR sum.
    axiom xor_sum_property:
      \forall int *a, int n;
        (xor_sum_range(a, 0, n - 1) ==
         \f_xor_all_elements_occurring_odd_times(a, n)
        );

    // This logic function represents the conceptual XOR sum of elements that appear an odd number of times.
    // It's a high-level representation of what the function computes.
    logic integer \f_xor_all_elements_occurring_odd_times(int *a, int n) =
      \xor (\union integer k; 0 <= k < n && (\count integer i; 0 <= i < n && a[i] == a[k]) % 2 == 1; a[k]);
  }
*/

/*@
  requires n > 0;
  requires \valid_read(a + (0..n-1));
  assigns \nothing;

  // The result of the XOR sum will be the element that appears an odd number of times.
  // The XOR sum of all elements in the array will isolate the element(s) with odd occurrences.
  // If there's only one such element (as implied by the problem "the element"),
  // then the result will be exactly that element.
  ensures \result == xor_sum_range(a, 0, n - 1);
*/
int find_odd_occurrence(int *a, int n) {
    int res = 0;
    /*@
      loop invariant 0 <= i <= n;
      loop invariant res == xor_sum_range(a, 0, i - 1); // Accumulates XOR sum up to i-1
      loop assigns res, i;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        res = res ^ a[i];
    }
    return res;
}
