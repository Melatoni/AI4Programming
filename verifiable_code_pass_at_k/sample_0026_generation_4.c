// Task ID: 26
// Generation: 4

/*@
  // Rule II.1, II.2: Define an axiomatic block for recursive logic.
  axiomatic TupleList {
    logic integer get_first_element{L}(int* tuple);
    logic integer get_second_element{L}(int* tuple);

    axiom get_first_element_def{L}:
      \forall int* tuple;
      get_first_element(tuple) == tuple[0];

    axiom get_second_element_def{L}:
      \forall int* tuple;
      get_second_element(tuple) == tuple[1];

    // Rule II.1: Recursive logic to check if a specific key 'k' exists in the tuple list.
    // Rule I.3: `tuples` is a pointer to an array of 2-element arrays.
    logic boolean contains_key{L}(int (*tuples)[2], int count, int k);

    axiom contains_key_base{L}:
      \forall int (*tuples)[2], int k;
      contains_key(tuples, 0, k) == \false;

    axiom contains_key_recursive{L}:
      \forall int (*tuples)[2], int count, int k;
      count > 0 ==>
      contains_key(tuples, count, k) ==
      (get_first_element(tuples[count - 1]) == k || contains_key(tuples, count - 1, k));

    // Rule II.1: Recursive logic to check if all keys from 0 to k_max-1 are present.
    logic boolean all_keys_present{L}(int (*tuples)[2], int count, int k_max);

    axiom all_keys_present_base{L}:
      \forall int (*tuples)[2];
      all_keys_present(tuples, 0, 0) == \true;

    axiom all_keys_present_base_k_max_zero_empty_list{L}:
      \forall int (*tuples)[2], int count;
      count > 0 ==> all_keys_present(tuples, count, 0) == \true;

    axiom all_keys_present_recursive{L}:
      \forall int (*tuples)[2], int count, int k_max;
      k_max > 0 ==>
      all_keys_present(tuples, count, k_max) ==
      (contains_key(tuples, count, k_max - 1) && all_keys_present(tuples, count, k_max - 1));

    // Rule II.2: Helper axiom for `all_keys_present`
    // If all keys are present for `k_max`, and a new key `k_max` is present,
    // then all keys are present for `k_max + 1`.
    axiom all_keys_present_helper{L}:
      \forall int (*tuples)[2], int count, int k_max;
      k_max >= 0 && all_keys_present(tuples, count, k_max) && contains_key(tuples, count, k_max) ==>
      all_keys_present(tuples, count, k_max + 1);

    // Rule II.2: Helper axiom for `all_keys_present`
    // If a key `k` is present, it's also present in a larger list.
    axiom contains_key_monotonic{L}:
      \forall int (*tuples)[2], int count1, int count2, int k;
      0 <= count1 <= count2 && contains_key(tuples, count1, k) ==> contains_key(tuples, count2, k);

    // Rule II.2: Helper axiom for `all_keys_present`
    // If all keys are present in a smaller list, they are also present in a larger list.
    axiom all_keys_present_monotonic{L}:
      \forall int (*tuples)[2], int count1, int count2, int k_max;
      0 <= count1 <= count2 && all_keys_present(tuples, count1, k_max) ==> all_keys_present(tuples, count2, k_max);
  }
*/

/*@
  requires count >= 0;
  requires k_max >= 0;
  requires \valid_read_range(tuples[0], 0, count * 2 - 1); // Ensure tuples array is readable.
  // Rule II.5: Prevent potential overflow if k_max is excessively large.
  // Although not strictly an arithmetic overflow, it limits the logical range.
  requires k_max <= 1000; // Arbitrary reasonable limit for k_max
  
  assigns \nothing;
  
  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (all_keys_present(tuples, count, k_max)) <==> (esult == 1);
*/
// Rule I.2: Uses int for boolean return.
// Rule I.3: `tuples` parameter uses the correct pointer decay type.
int has_all_k_elements(int (*tuples)[2], int count, int k_max) {
    /*@
      loop invariant 0 <= i <= k_max;
      loop invariant \forall integer j; 0 <= j < i ==> contains_key(tuples, count, j);
      loop invariant (\forall integer j; 0 <= j < i ==> contains_key(tuples, count, j)) <==> all_keys_present(tuples, count, i);
      loop assigns i;
      // Rule II.4: A loop variant is mandatory for termination.
      loop variant k_max - i;
    */
    for (int i = 0; i < k_max; i++) {
        // Check if key 'i' exists in the list
        int key_found = 0; // Rule I.2: Use int for boolean.
        /*@
          loop invariant 0 <= j <= count;
          loop invariant \forall integer l; 0 <= l < j ==> get_first_element(tuples[l]) != i;
          loop invariant key_found == (\exists integer l; 0 <= l < j && get_first_element(tuples[l]) == i);
          loop assigns j, key_found;
          loop variant count - j;
        */
        for (int j = 0; j < count; j++) {
            if (tuples[j][0] == i) {
                key_found = 1;
                break;
            }
        }
        if (key_found == 0) {
            return 0; // Key 'i' not found, so not all keys are present.
        }
    }
    return 1; // All keys from 0 to k_max-1 were found.
}
