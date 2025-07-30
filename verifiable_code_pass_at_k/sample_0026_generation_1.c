// Task ID: 26
// Generation: 1

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This logic function checks if a specific element 'e' exists in the array 'a' up to index 'idx'.
  axiomatic HasElement {
    logic boolean has_element_at_idx{L}(int[] a, int idx, int e);

    axiom has_element_at_idx_base{L}:
      \forall int[] a, int e;
        has_element_at_idx(a, -1, e) == \false;

    axiom has_element_at_idx_recursive{L}:
      \forall int[] a, int idx, int e;
        idx >= 0 ==> has_element_at_idx(a, idx, e) == (a[idx] == e || has_element_at_idx(a, idx - 1, e));
  }
*/

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This logic function checks if all integers from 0 to k-1 exist in the array 'arr'.
  axiomatic HasAllKElements {
    logic boolean has_all_k_elements{L}(int[] arr, int size, int k);

    // Rule II.2: Helper axiom for the base case. If k is 0 or less, it trivially has all elements.
    axiom has_all_k_elements_base_k_zero{L}:
      \forall int[] arr, int size, int k;
        k <= 0 ==> has_all_k_elements(arr, size, k) == \true;

    // Rule II.2: Helper axiom for the recursive step.
    // It has all k elements if it has k-1 elements AND the (k-1)th element itself.
    axiom has_all_k_elements_recursive{L}:
      \forall int[] arr, int size, int k;
        k > 0 ==> has_all_k_elements(arr, size, k) == (has_all_k_elements(arr, size, k - 1) && has_element_at_idx(arr, size - 1, k - 1));
  }
*/


/*@
  requires size >= 0;
  requires k >= 0;
  // Rule II.5: Prevent out-of-bounds access if k is large.
  // This constraint ensures that k will not cause issues if it's much larger than size,
  // though the logic handles it by returning false.
  // For the `has_element_at_idx` call `k-1` to be valid, we need `k-1 >= 0`, i.e., `k >= 1`.
  // If k is 0, the recursive logic handles it as true.
  // So, if k > 0, we need to ensure that the element k-1 could potentially exist.
  // Actually, the `has_element_at_idx` logic itself handles out-of-bounds `idx` by returning false.
  // So a specific constraint on k relative to size is not strictly needed for correctness but can help WP.
  // Let's add a practical constraint for array access if k elements are expected.
  // If k > 0, then k-1 must be a valid element we could look for.
  // This isn't a direct RTE, but guides the prover.
  // For `has_element_at_idx(arr, size - 1, k - 1)` to be meaningful, size must be >= 1 if k >= 1.
  // The logic `has_element_at_idx(arr, size - 1, k - 1)` implicitly handles `size - 1 < 0` by returning `false`.

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  ensures has_all_k_elements(list, size, k) <==> (result == 1);
*/
int has_all_k_elements_in_list(int* list, int size, int k) { // Rule I.2: int for boolean.
    int found_count = 0; // Represents how many distinct elements from 0 to k-1 have been found.

    /*@
      loop invariant 0 <= i <= k;
      // Invariant: If a number `j` from `0` to `k-1` has been found in `list[0..size-1]`,
      // then `is_found[j]` is 1. Otherwise, it's 0.
      loop invariant \forall integer j; 0 <= j < k ==> (
        is_found[j] == 1 <==> has_element_at_idx(list, size - 1, j)
      );
      loop assigns i, found_count, is_found[0..k-1];
      loop variant k - i;
    */
    for (int i = 0; i < k; ++i) {
        int current_element_to_find = i;
        int found_current_element = 0; // Rule I.2: int for boolean.

        /*@
          loop invariant 0 <= j <= size;
          loop invariant found_current_element == 1 <==> has_element_at_idx(list, j - 1, current_element_to_find);
          loop assigns j, found_current_element;
          loop variant size - j;
        */
        for (int j = 0; j < size; ++j) {
            if (list[j] == current_element_to_find) {
                found_current_element = 1;
                break; // Found it, no need to check further.
            }
        }

        if (!found_current_element) { // Rule I.2: int for boolean.
            return 0; // If any element from 0 to k-1 is not found, return false.
        }
    }

    // If the loop completes, it means all elements from 0 to k-1 were found.
    return 1;
}
