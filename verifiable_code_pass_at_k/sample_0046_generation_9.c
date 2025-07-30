// Task ID: 46
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic AllDifferent {
    logic boolean all_different_upto(int* arr, int size, int k);

    axiom all_different_upto_base:
      \forall int* arr, int size;
        all_different_upto(arr, size, 0);

    axiom all_different_upto_recursive:
      \forall int* arr, int size, int k;
        0 < k && k <= size ==>
        (all_different_upto(arr, size, k) <==>
          (all_different_upto(arr, size, k - 1) &&
           (\forall integer i; 0 <= i < k - 1 ==> arr[i] != arr[k-1])
          )
        );

    // Helper axiom: if all_different_upto(arr, size, k) is true, then
    // all elements within 0..k-1 are pairwise distinct.
    axiom all_different_upto_implies_pairwise_distinct:
      \forall int* arr, int size, int k, integer i, integer j;
        0 <= i < j < k && all_different_upto(arr, size, k) ==> arr[i] != arr[j];

    // Helper axiom: if all_different_upto(arr, size, k) is false, then
    // there exist i, j < k such that arr[i] == arr[j].
    axiom all_different_upto_implies_not_pairwise_distinct:
      \forall int* arr, int size, int k;
        0 < k && !all_different_upto(arr, size, k) ==>
        (\exists integer i, j; 0 <= i < j < k && arr[i] == arr[j]);
  }
*/

/*@
  requires size >= 0;
  requires \valid_read(arr + (0..size-1));

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // Rule I.2: Returns int (1 for true, 0 for false).
  ensures (\result == 1) <==> all_different_upto(arr, size, size);
*/
int are_all_elements_different(int* arr, int size) {
    /*@
      loop invariant 0 <= i <= size;
      loop invariant all_different_upto(arr, size, i);
      loop assigns i;
      loop variant size - i;
    */
    for (int i = 0; i < size; ++i) {
        /*@
          loop invariant i <= j <= size;
          loop invariant \forall integer k; i <= k < j ==> arr[i] != arr[k];
          loop assigns j;
          loop variant size - j;
        */
        for (int j = i + 1; j < size; ++j) {
            if (arr[i] == arr[j]) {
                return 0; // Found a duplicate
            }
        }
    }
    return 1; // No duplicates found
}
