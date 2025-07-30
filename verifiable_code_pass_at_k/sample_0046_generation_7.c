// Task ID: 46
// Generation: 7

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
  axiomatic AllDifferent {
    logic boolean all_different_aux(int* arr, int start, int end);

    axiom all_different_base:
      \forall int* arr, int start, int end;
        start >= end ==> all_different_aux(arr, start, end) == \true;

    axiom all_different_recursive:
      \forall int* arr, int start, int end;
        start < end ==> (all_different_aux(arr, start, end) ==
                         (\forall integer k; start < k <= end ==> arr[start] != arr[k]) &&
                         all_different_aux(arr, start + 1, end));

    // Helper axiom: If a subarray is all different, then any smaller subarray starting from the same point is also all different.
    axiom all_different_prefix_subset:
      \forall int* arr, int start, int end, int new_end;
        start <= new_end <= end && all_different_aux(arr, start, end) ==> all_different_aux(arr, start, new_end);

    // Helper axiom: If a subarray is all different, then any smaller subarray ending at the same point is also all different.
    axiom all_different_suffix_subset:
      \forall int* arr, int start, int end, int new_start;
        start <= new_start <= end && all_different_aux(arr, start, end) ==> all_different_aux(arr, new_start, end);

    // Helper axiom: If all_different_aux is true for a range, it implies no duplicates within that range.
    axiom all_different_no_duplicates:
      \forall int* arr, int start, int end;
        all_different_aux(arr, start, end) ==> (\forall integer i, j; start <= i < j <= end ==> arr[i] != arr[j]);

    // Helper axiom: If there are duplicates, then all_different_aux is false.
    axiom all_different_has_duplicates:
      \forall int* arr, int start, int end;
        (\exists integer i, j; start <= i < j <= end && arr[i] == arr[j]) ==> all_different_aux(arr, start, end) == \false;
  }
*/

/*@
  requires n >= 0;
  // Rule I.3: Array pointer decay. arr is int*
  // Rule II.3: Ensures clause uses logical equivalence.
  ensures (\result == 1) <==> all_different_aux(arr, 0, n - 1);
  assigns \nothing;
*/
int are_all_numbers_different(int* arr, int n) {
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> (\forall integer j; k < j < n ==> arr[k] != arr[j]);
      loop invariant all_different_aux(arr, i, n - 1) <==> (
        (\forall integer x; i <= x < n ==> (\forall integer y; x < y < n ==> arr[x] != arr[y]))
      );
      loop assigns i, j;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop invariant i + 1 <= j <= n;
          loop invariant \forall integer k; i < k < j ==> arr[i] != arr[k];
          loop assigns j;
          loop variant n - j;
        */
        for (int j = i + 1; j < n; j++) {
            if (arr[i] == arr[j]) {
                return 0; // Found a duplicate
            }
        }
    }
    return 1; // No duplicates found
}
