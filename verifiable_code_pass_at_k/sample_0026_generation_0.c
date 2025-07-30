// Task ID: 26
// Generation: 0

/*@
  // Rule I.1: No standard libraries, so use ACSL constants directly if needed.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay applied to `list` parameter.

  // Rule II.1: Define recursive logic for complex properties.
  // Rule II.2: Add helper axioms for recursive functions.
  // Rule II.3: Use logical equivalence `<==>` for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.

  // Axiomatic block to define properties of the tuple list.
  // This helps reason about the presence of elements.
*/
/*@
  axiomatic TupleListProperties {
    logic boolean is_present(int val, int* list, int size);

    // Base case: If size is 0, value is not present.
    axiom is_present_base:
      \forall int val, int* list;
        !is_present(val, list, 0);

    // Recursive case: Value is present if it's the last element OR present in the rest of the list.
    axiom is_present_recursive:
      \forall int val, int* list, int size;
        size > 0 ==> (is_present(val, list, size) <==> (list[size - 1] == val || is_present(val, list, size - 1)));

    // Helper axiom: If a value is present in a sublist, it's present in the larger list.
    axiom is_present_sublist_implies_larger:
      \forall int val, int* list, int sub_size, int full_size;
        0 <= sub_size <= full_size && is_present(val, list, sub_size) ==> is_present(val, list, full_size);

    // Helper axiom: If a value is not present in a larger list, it's not present in any sublist.
    axiom is_not_present_larger_implies_sublist:
      \forall int val, int* list, int sub_size, int full_size;
        0 <= sub_size <= full_size && !is_present(val, list, full_size) ==> !is_present(val, list, sub_size);

    // Logic function to check if all elements from 0 to k-1 are present in the list.
    logic boolean all_k_elements_present(int k, int* list, int size);

    // Base case for all_k_elements_present: If k is 0, all (zero) elements are present.
    axiom all_k_elements_present_base:
      \forall int* list, int size;
        all_k_elements_present(0, list, size);

    // Recursive case for all_k_elements_present:
    // All k elements are present if (k-1) is present AND all elements up to k-1 are present.
    axiom all_k_elements_present_recursive:
      \forall int k, int* list, int size;
        k > 0 ==> (all_k_elements_present(k, list, size) <==> (is_present(k - 1, list, size) && all_k_elements_present(k - 1, list, size)));

    // Helper axiom: If all k elements are present, then all elements less than k are also present.
    axiom all_k_elements_present_monotonicity:
      \forall int k_prime, int k, int* list, int size;
        0 <= k_prime <= k && all_k_elements_present(k, list, size) ==> all_k_elements_present(k_prime, list, size);

    // Helper axiom: If a value 'v' is present, and all elements up to 'k' are present,
    // and 'v' is one of those elements (i.e., 'v < k'), then 'v' is present. (Redundant but can help prover)
    axiom all_k_elements_present_implies_individual_presence:
      \forall int k, int* list, int size, int v;
        0 <= v < k && all_k_elements_present(k, list, size) ==> is_present(v, list, size);

  }
*/

/*@
  requires k >= 0;
  requires size >= 0;
  // Rule II.5: Prevent RTE - ensure list is not null if size > 0.
  requires size == 0 || \valid_read_range(list, 0, size - 1);
  // Rule II.5: Prevent RTE - ensure elements in list are non-negative for comparison with k.
  // This constraint is critical for the `is_present` logic and the problem context (k elements 0 to k-1).
  requires \forall integer i; 0 <= i < size ==> list[i] >= 0;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return.
  ensures (all_k_elements_present(k, list, size)) <==> (\result == 1);
*/
int has_all_k_elements(int k, int* list, int size) {
    /*@
      loop invariant 0 <= i <= k;
      // All elements from 0 to i-1 have been found (if i > 0).
      loop invariant \forall integer j; 0 <= j < i ==> is_present(j, list, size);
      // Alternative: What we have found so far means all elements up to `i` (exclusive) are present.
      loop invariant all_k_elements_present(i, list, size);

      loop assigns i;
      loop variant k - i;
    */
    for (int i = 0; i < k; i++) {
        int found_i = 0;
        /*@
          loop invariant 0 <= j <= size;
          loop invariant \forall integer l; 0 <= l < j ==> list[l] != i; // i has not been found in list[0..j-1]
          loop invariant found_i == 0; // If found_i was already 1, we would have broken out.
          loop assigns j, found_i;
          loop variant size - j;
        */
        for (int j = 0; j < size; j++) {
            if (list[j] == i) {
                found_i = 1;
                break;
            }
        }
        if (found_i == 0) {
            return 0; // Element i was not found
        }
    }
    return 1; // All elements from 0 to k-1 were found
}
