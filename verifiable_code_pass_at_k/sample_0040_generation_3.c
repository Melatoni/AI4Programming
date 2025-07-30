// Task ID: 40
// Generation: 3

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Use int for boolean-like return values.
  // Rule I.3: Array parameters decay to pointers.

  // Rule II.1, II.2: Define axiomatic for properties over sequences.
  // We need to count frequencies. Let's define a logic function to count
  // occurrences of an element in a flat array.
*/
/*@ axiomatic Frequencies {
  logic integer count_in_array{L}(int* arr, integer len, int val) reads arr[0..len-1];

  axiom count_in_array_empty{L}:
    \forall int* arr, int val;
      count_in_array(arr, 0, val) == 0;

  axiom count_in_array_rec{L}:
    \forall int* arr, integer len, int val;
      len > 0 ==> count_in_array(arr, len, val) ==
        (if arr[len-1] == val then 1 else 0) + count_in_array(arr, len-1, val);

  // Helper axiom: if an element is not in the array, its count is 0.
  // This helps the prover relate the count to the presence of elements.
  axiom count_in_array_not_present{L}:
    \forall int* arr, integer len, int val;
      (\forall integer i; 0 <= i < len ==> arr[i] != val) ==> count_in_array(arr, len, val) == 0;

  // Helper axiom: sum of counts for distinct elements is total length.
  // Not directly used in this problem, but good practice for frequency analysis.
  // axiom count_in_array_sum_distinct{L}:
  //   \forall int* arr, integer len, int* distinct_vals, integer distinct_len;
  //     (\forall integer i, j; 0 <= i < j < distinct_len ==> distinct_vals[i] != distinct_vals[j]) ==>
  //     (\sum integer i; 0 <= i < distinct_len; count_in_array(arr, len, distinct_vals[i])) == len;

  // We need to count occurrences of an element in a list of lists.
  // This means iterating through each sublist and summing up counts.
  logic integer count_in_list_of_lists{L}(int* lists[], integer num_lists, integer list_lengths[], int val) reads lists[0..num_lists-1], list_lengths[0..num_lists-1];

  axiom count_in_list_of_lists_empty{L}:
    \forall int* lists[], integer num_lists, integer list_lengths[], int val;
      count_in_list_of_lists(lists, 0, list_lengths, val) == 0;

  axiom count_in_list_of_lists_rec{L}:
    \forall int* lists[], integer num_lists, integer list_lengths[], int val;
      num_lists > 0 ==> count_in_list_of_lists(lists, num_lists, list_lengths, val) ==
        count_in_array(lists[num_lists-1], list_lengths[num_lists-1], val) +
        count_in_list_of_lists(lists, num_lists-1, list_lengths, val);

  // Helper axiom: if an element is not in any sublist, its total count is 0.
  axiom count_in_list_of_lists_not_present{L}:
    \forall int* lists[], integer num_lists, integer list_lengths[], int val;
      (\forall integer i; 0 <= i < num_lists ==> (\forall integer j; 0 <= j < list_lengths[i] ==> lists[i][j] != val)) ==>
      count_in_list_of_lists(lists, num_lists, list_lengths, val) == 0;
}
*/

/*@
  requires num_lists >= 0;
  requires \valid(lists + (0..num_lists-1));
  requires \valid(list_lengths + (0..num_lists-1));

  // Each sublist pointer must be valid for its specified length.
  requires \forall integer i; 0 <= i < num_lists ==> \valid(lists[i] + (0..list_lengths[i]-1));
  requires \forall integer i; 0 <= i < num_lists ==> list_lengths[i] >= 0;

  // The 'frequencies' array must be large enough to store frequencies for all elements.
  // For simplicity, we assume elements are within a non-negative range [0, max_val].
  // This requires a pre-defined maximum value for elements.
  requires max_val >= 0;
  requires \valid(frequencies + (0..max_val));

  // The 'frequencies' array should be initialized to zeros or not contain garbage.
  // Frama-C typically assumes uninitialized local arrays. For global/static, they are zero.
  // For a function that *populates* frequencies, we don't need to require its initial state.
  // However, we must ensure that the function does not access out-of-bounds indices in 'frequencies'.
  requires \forall integer i; 0 <= i < num_lists ==> (\forall integer j; 0 <= j < list_lengths[i] ==> lists[i][j] >= 0 && lists[i][j] <= max_val);

  assigns frequencies[0..max_val];

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // For each possible value 'v' from 0 to max_val, the frequency in the output
  // array 'frequencies[v]' must be equal to the total count of 'v' in the input lists.
  ensures \forall integer v; 0 <= v <= max_val ==> frequencies[v] == count_in_list_of_lists(lists, num_lists, list_lengths, v);
*/
void find_element_frequencies(int* lists[], int num_lists, int list_lengths[], int max_val, int frequencies[]) {
    // Initialize frequencies array to zeros
    /*@
      loop invariant 0 <= i <= max_val + 1;
      loop invariant \forall integer k; 0 <= k < i ==> frequencies[k] == 0;
      loop assigns frequencies[0..max_val];
      loop variant max_val - i;
    */
    for (int i = 0; i <= max_val; i++) {
        frequencies[i] = 0;
    }

    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant \forall integer k; 0 <= k < i ==>
        (\forall integer v; 0 <= v <= max_val ==>
          frequencies[v] == count_in_list_of_lists(lists, k, list_lengths, v));

      loop assigns frequencies[0..max_val], i;
      loop variant num_lists - i;
    */
    for (int i = 0; i < num_lists; i++) {
        int* current_list = lists[i];
        int current_list_length = list_lengths[i];

        /*@
          loop invariant 0 <= j <= current_list_length;
          // The frequencies array correctly reflects the counts from lists[0..i-1]
          // plus the counts from current_list[0..j-1].
          loop invariant \forall integer v; 0 <= v <= max_val ==>
            frequencies[v] ==
            count_in_list_of_lists(lists, i, list_lengths, v) +
            count_in_array(current_list, j, v);

          loop assigns frequencies[0..max_val], j;
          loop variant current_list_length - j;
        */
        for (int j = 0; j < current_list_length; j++) {
            int element = current_list[j];
            // Rule II.5: Prevent RTE. The requires clause ensures element is within [0, max_val].
            frequencies[element]++;
        }
    }
}
