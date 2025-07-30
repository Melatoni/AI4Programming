// Task ID: 22
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in ACSL.

  // Rule II.1: Recursive logic for complexity (not directly needed for this problem).
  // Rule II.2: Helper axioms (not directly needed for this problem).

  // Define a logic function to check if an element is duplicated before a certain index.
  // This helps in constructing the postcondition.
  axiomatic FirstDuplicateLogic {
    logic boolean is_duplicated_before(int* arr, int val, int index, int len);

    axiom is_duplicated_before_base:
      \forall int* arr, int val, int len;
        0 <= len ==> is_duplicated_before(arr, val, 0, len) == \false;

    axiom is_duplicated_before_step:
      \forall int* arr, int val, int index, int len;
        0 <= index < len ==>
        is_duplicated_before(arr, val, index + 1, len) ==
        (is_duplicated_before(arr, val, index, len) || (arr[index] == val));
  }
*/

/*@
  requires N >= 0;
  requires \valid_read(arr + (0..N-1));

  // Rule II.5: Prevent runtime errors.
  // No specific overflow checks needed for this problem beyond array bounds.

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like functions.
  // The function returns the first duplicate element, or 0 if no duplicates exist.
  // We define "first duplicate" as the element with the smallest index 'j' such that
  // arr[j] is equal to some arr[k] where k < j.
  ensures (\exists integer j; 0 <= j < N && (\exists integer k; 0 <= k < j && arr[k] == arr[j]) &&
           (\forall integer p; 0 <= p < j ==> !(\exists integer q; 0 <= q < p && arr[q] == arr[p])))
          <==> (\result != 0);

  // If a duplicate is found, \result must be that duplicate.
  ensures (\result != 0) ==>
          (\exists integer j; 0 <= j < N && arr[j] == \result &&
           (\exists integer k; 0 <= k < j && arr[k] == arr[j]) &&
           (\forall integer p; 0 <= p < j ==> !(\exists integer q; 0 <= q < p && arr[q] == arr[p])));

  // If no duplicate is found, \result must be 0.
  ensures (\result == 0) ==>
          (\forall integer j; 0 <= j < N ==> !(\exists integer k; 0 <= k < j && arr[k] == arr[j]));
*/
int find_first_duplicate(int* arr, int N) {
    /*@
      loop invariant 0 <= i <= N;
      // All elements processed so far (arr[0] to arr[i-1]) do not have a duplicate before them.
      // Or, if a duplicate was found and returned, the loop would have terminated.
      loop invariant \forall integer p; 0 <= p < i ==> !(\exists integer q; 0 <= q < p && arr[q] == arr[p]);
      loop assigns i;
      // Rule II.4: Loop variant for termination.
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        /*@
          loop invariant 0 <= j <= i;
          // No duplicate found for arr[i] among arr[0] to arr[j-1].
          loop invariant \forall integer k; 0 <= k < j ==> arr[k] != arr[i];
          loop assigns j;
          loop variant i - j;
        */
        for (int j = 0; j < i; j++) {
            if (arr[j] == arr[i]) {
                return arr[i]; // Rule I.2: Returns the duplicate value.
            }
        }
    }
    return 0; // Rule I.2: Returns 0 if no duplicate is found.
}
