// Task ID: 22
// Generation: 6

/*@
  // Rule II.1, II.2: Define an axiomatic block for recursive logic.
  axiomatic FirstDuplicate {
    // Defines whether an element `x` has appeared before index `idx`.
    logic boolean has_appeared_before(int* arr, int x, int idx) reads arr[0..idx-1];

    axiom has_appeared_before_base:
      \forall int* arr, int x; has_appeared_before(arr, x, 0) == \false;

    axiom has_appeared_before_recursive:
      \forall int* arr, int x, integer idx;
        idx > 0 ==> (has_appeared_before(arr, x, idx) ==
                     (arr[idx-1] == x || has_appeared_before(arr, x, idx-1)));

    // Defines the first index `k` where arr[k] has a duplicate before it.
    logic integer first_duplicate_index(int* arr, integer len);

    // Rule II.2: Helper axiom for first_duplicate_index when no duplicate exists.
    axiom first_duplicate_index_no_duplicate:
      \forall int* arr, integer len;
        (\forall integer i; 0 <= i < len ==> !has_appeared_before(arr, arr[i], i)) ==>
        first_duplicate_index(arr, len) == -1; // -1 signifies no duplicate

    // Rule II.2: Helper axiom for first_duplicate_index when a duplicate exists.
    axiom first_duplicate_index_with_duplicate:
      \forall int* arr, integer len;
        (\exists integer i; 0 <= i < len && has_appeared_before(arr, arr[i], i)) ==>
        (0 <= first_duplicate_index(arr, len) < len &&
         has_appeared_before(arr, arr[first_duplicate_index(arr, len)], first_duplicate_index(arr, len)) &&
         (\forall integer k; 0 <= k < first_duplicate_index(arr, len) ==> !has_appeared_before(arr, arr[k], k)));
  }
*/

/*@
  requires valid_read_array(arr, len);
  requires len >= 0;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.1: No C-style ternary in ACSL.
  ensures \result == (if first_duplicate_index(arr, len) != -1 then arr[first_duplicate_index(arr, len)] else -1);
*/
int find_first_duplicate(int* arr, int len) {
  /*@
    loop invariant 0 <= i <= len;
    // The elements arr[0..i-1] have been processed.
    // If a duplicate was found, it must be the first one.
    loop invariant (\forall integer k; 0 <= k < i ==> !has_appeared_before(arr, arr[k], k)) ||
                   (found_duplicate == 1 &&
                    \exists integer idx; 0 <= idx < i && has_appeared_before(arr, arr[idx], idx) &&
                    arr[idx] == result_val &&
                    (\forall integer k; 0 <= k < idx ==> !has_appeared_before(arr, arr[k], k)));

    // Ensure that if found_duplicate is 1, result_val holds the first duplicate found so far.
    loop invariant (found_duplicate == 1) ==>
                   (\exists integer k; 0 <= k < i && has_appeared_before(arr, arr[k], k) && arr[k] == result_val);

    // Ensure that if found_duplicate is 0, no duplicate has been found yet.
    loop invariant (found_duplicate == 0) ==>
                   (\forall integer k; 0 <= k < i ==> !has_appeared_before(arr, arr[k], k));

    loop assigns i, found_duplicate, result_val;
    loop variant len - i; // Rule II.4: Mandatory loop variant.
  */
  for (int i = 0; i < len; i++) {
    /*@
      loop invariant 0 <= j <= i;
      // Checks if arr[i] has appeared in arr[0..j-1]
      loop invariant (found_current_duplicate == 1) ==>
                     (\exists integer k; 0 <= k < j && arr[k] == arr[i]);
      loop invariant (found_current_duplicate == 0) ==>
                     (\forall integer k; 0 <= k < j && arr[k] != arr[i]);
      loop assigns j, found_current_duplicate;
      loop variant i - j;
    */
    int found_current_duplicate = 0; // Rule I.2: Use int for boolean.
    /*@
      loop invariant 0 <= j <= i;
      // If found_current_duplicate is 1, then arr[i] is equal to some arr[k] for k < j.
      loop invariant (found_current_duplicate == 1) ==> (\exists integer k; 0 <= k < j && arr[k] == arr[i]);
      // If found_current_duplicate is 0, then arr[i] is not equal to any arr[k] for k < j.
      loop invariant (found_current_duplicate == 0) ==> (\forall integer k; 0 <= k < j ==> arr[k] != arr[i]);
      loop assigns j, found_current_duplicate;
      loop variant i - j;
    */
    for (int j = 0; j < i; j++) {
      if (arr[j] == arr[i]) {
        found_current_duplicate = 1;
        break;
      }
    }

    if (found_current_duplicate == 1) {
      return arr[i];
    }
  }

  return -1; // No duplicate found
}
