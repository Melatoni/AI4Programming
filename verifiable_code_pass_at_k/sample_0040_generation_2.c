// Task ID: 40
// Generation: 2

/*@
  // Rule I.1: No standard libraries. ACSL constants are implicitly known.
  // Rule I.2: Using 'int' for boolean-like values.
  // Rule I.3: Array pointer decay.

  // Axiomatic block for recursive logic and helper axioms.
  // Rule II.1: Recursive logic for complex properties.
  // Rule II.2: Helper axioms are CRITICAL.
*/
/*@
  axiomatic ListProperties {
    // Defines a property that an element 'x' exists in a sublist 'sublist' up to index 'len'.
    logic boolean exists_in_sublist(int x, int* sublist, int len) =
      len <= 0 ? \false :
      (sublist[len-1] == x) || exists_in_sublist(x, sublist, len-1);

    // Defines a property that an element 'x' exists in any of the lists in 'list_of_lists'.
    logic boolean exists_in_list_of_lists(int x, int** list_of_lists, int num_lists, int* sublist_lengths) =
      num_lists <= 0 ? \false :
      exists_in_sublist(x, list_of_lists[num_lists-1], sublist_lengths[num_lists-1]) ||
      exists_in_list_of_lists(x, list_of_lists, num_lists-1, sublist_lengths);

    // Defines the frequency of an element 'x' in a single sublist.
    logic integer count_in_sublist(int x, int* sublist, int len) =
      len <= 0 ? 0 :
      (sublist[len-1] == x ? 1 : 0) + count_in_sublist(x, sublist, len-1);

    // Defines the total frequency of an element 'x' across all sublists.
    logic integer total_count(int x, int** list_of_lists, int num_lists, int* sublist_lengths) =
      num_lists <= 0 ? 0 :
      count_in_sublist(x, list_of_lists[num_lists-1], sublist_lengths[num_lists-1]) +
      total_count(x, list_of_lists, num_lists-1, sublist_lengths);

    // Helper axiom: If an element exists in a list of lists, its total count must be at least 1.
    axiom total_count_positive_if_exists:
      \forall int x, int** l, int n, int* sl;
        exists_in_list_of_lists(x, l, n, sl) ==> total_count(x, l, n, sl) >= 1;

    // Helper axiom: If an element does not exist, its total count must be 0.
    axiom total_count_zero_if_not_exists:
      \forall int x, int** l, int n, int* sl;
        !exists_in_list_of_lists(x, l, n, sl) ==> total_count(x, l, n, sl) == 0;
  }
*/

/*@
  requires num_lists >= 0;
  requires \valid_read_array(list_of_lists, num_lists);
  requires \valid_read_array(sublist_lengths, num_lists);

  // Each sublist pointer must be valid for its given length.
  requires \forall integer k; 0 <= k < num_lists ==> \valid_read_array(list_of_lists[k], sublist_lengths[k]);

  requires num_distinct_elements >= 0;
  requires \valid_write_array(distinct_elements, num_distinct_elements);
  requires \valid_write_array(frequencies, num_distinct_elements);

  // Each element in distinct_elements must be unique.
  requires \forall integer i, j; 0 <= i < j < num_distinct_elements ==> distinct_elements[i] != distinct_elements[j];

  // Each distinct element must actually exist in the list of lists.
  // This simplifies the postcondition by ensuring we are only counting elements that are present.
  requires \forall integer i; 0 <= i < num_distinct_elements ==> exists_in_list_of_lists(distinct_elements[i], list_of_lists, num_lists, sublist_lengths);

  assigns distinct_elements[0..num_distinct_elements-1],
          frequencies[0..num_distinct_elements-1];

  // Rule II.3: Ensures clause for boolean-like functions (though this returns void,
  //            it sets output arrays, so the postcondition should reflect the outcome).
  // This ensures that for each distinct element, its frequency is correctly calculated.
  ensures \forall integer i; 0 <= i < num_distinct_elements ==>
    frequencies[i] == total_count(distinct_elements[i], list_of_lists, num_lists, sublist_lengths);
*/
void find_element_frequencies(
    int** list_of_lists,
    int num_lists,
    int* sublist_lengths,
    int* distinct_elements,
    int num_distinct_elements,
    int* frequencies
) {
    /*@
      loop invariant 0 <= i <= num_distinct_elements;
      loop invariant \forall integer k; 0 <= k < i ==>
        frequencies[k] == total_count(distinct_elements[k], list_of_lists, num_lists, sublist_lengths);
      loop assigns i, frequencies[0..num_distinct_elements-1];
      // Rule II.4: Mandatory loop variant.
      loop variant num_distinct_elements - i;
    */
    for (int i = 0; i < num_distinct_elements; i++) {
        int current_element = distinct_elements[i];
        int current_frequency = 0;

        /*@
          loop invariant 0 <= j <= num_lists;
          loop invariant current_frequency ==
            total_count(current_element, list_of_lists, j, sublist_lengths);
          loop assigns j, current_frequency;
          loop variant num_lists - j;
        */
        for (int j = 0; j < num_lists; j++) {
            int* sublist = list_of_lists[j];
            int sublist_len = sublist_lengths[j];

            /*@
              loop invariant 0 <= k <= sublist_len;
              loop invariant current_frequency ==
                (\sum integer x; 0 <= x < j; count_in_sublist(current_element, list_of_lists[x], sublist_lengths[x])) +
                count_in_sublist(current_element, sublist, k);
              loop assigns k, current_frequency;
              loop variant sublist_len - k;
            */
            for (int k = 0; k < sublist_len; k++) {
                if (sublist[k] == current_element) {
                    // Rule II.5: Prevent overflow if frequencies can be very high.
                    // Assuming frequency won't exceed INT_MAX for typical use cases.
                    // If it could, a requires clause on total_count range would be needed.
                    current_frequency++;
                }
            }
        }
        frequencies[i] = current_frequency;
    }
}
