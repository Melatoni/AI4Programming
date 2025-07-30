// Task ID: 22
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Axiomatic block for recursive logic.
  // Rule II.1: Use recursive logic for complexity.
  // Rule II.2: Helper axioms are CRITICAL.
*/
/*@
  axiomatic FirstDuplicate {
    logic integer first_duplicate_idx(int* arr, integer len);

    axiom first_duplicate_idx_base:
      \forall int* arr, integer len; len <= 1 ==> first_duplicate_idx(arr, len) == -1;

    axiom first_duplicate_idx_recursive:
      \forall int* arr, integer len; len > 1 ==>
        first_duplicate_idx(arr, len) ==
          (
            \exists integer j; 0 <= j < len - 1 && arr[j] == arr[len - 1]
            ? len - 1
            : first_duplicate_idx(arr, len - 1)
          );

    // Helper axiom: if a duplicate exists at index k, then the first duplicate index is <= k.
    axiom first_duplicate_helper_1:
      \forall int* arr, integer len, integer k;
        0 <= k < len && (\exists integer j; 0 <= j < k && arr[j] == arr[k]) ==>
        first_duplicate_idx(arr, len) <= k;

    // Helper axiom: if the first duplicate index is k, then arr[k] is the first duplicate.
    axiom first_duplicate_helper_2:
      \forall int* arr, integer len, integer k;
        first_duplicate_idx(arr, len) == k && k != -1 ==>
        (\exists integer j; 0 <= j < k && arr[j] == arr[k]) &&
        (\forall integer l; k < l < len ==> !(\exists integer m; 0 <= m < l && arr[m] == arr[l]));

    // Helper axiom: if no duplicate exists, first_duplicate_idx is -1.
    axiom first_duplicate_helper_3:
      \forall int* arr, integer len;
        (\forall integer i, j; 0 <= i < j < len ==> arr[i] != arr[j]) ==>
        first_duplicate_idx(arr, len) == -1;
  }
*/

/*@
  requires \valid_read_range(arr, 0, len - 1);
  requires len >= 0;

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like functions.
  // Rule I.2: Result is an integer representing an index. -1 means no duplicate.
  ensures \result == first_duplicate_idx(arr, len);
*/
int find_first_duplicate(int* arr, int len) {
    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer k; 0 <= k < i ==>
                       (\forall integer j; 0 <= j < k ==> arr[j] != arr[k]);
      loop invariant (\forall integer x; 0 <= x < i ==>
                       (\forall integer y; 0 <= y < x ==> arr[x] != arr[y]));
      loop assigns i, j;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        /*@
          loop invariant 0 <= j <= i;
          loop invariant \forall integer k; 0 <= k < j ==> arr[k] != arr[i];
          loop assigns j;
          loop variant i - j;
        */
        for (int j = 0; j < i; j++) {
            if (arr[j] == arr[i]) {
                return i;
            }
        }
    }
    return -1; // No duplicate found
}
