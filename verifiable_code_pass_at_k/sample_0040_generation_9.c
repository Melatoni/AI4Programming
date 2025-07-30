// Task ID: 40
// Generation: 9

/*@
  // Axiomatic definition for counting occurrences of a value in an array.
  // This replaces the need for a \sum or similar complex construct.
  axiomatic CountOccurrences {
    logic integer count_val{L}(int* arr, int size, int val);

    axiom count_val_empty{L}:
      \forall int val; count_val(arr, 0, val) == 0;

    axiom count_val_recursive{L}:
      \forall int* arr, int size, int val;
      size > 0 ==> count_val(arr, size, val) ==
        (if arr[size - 1] == val then 1 else 0) + count_val(arr, size - 1, val);
  }
*/

/*@
  // Axiomatic definition for counting total occurrences of a value across a list of lists.
  axiomatic CountTotalOccurrences {
    logic integer count_total_val{L}(int** lists, int* list_sizes, int num_lists, int val);

    axiom count_total_val_empty{L}:
      \forall int val; count_total_val(lists, list_sizes, 0, val) == 0;

    axiom count_total_val_recursive{L}:
      \forall int** lists, int* list_sizes, int num_lists, int val;
      num_lists > 0 ==> count_total_val(lists, list_sizes, num_lists, val) ==
        count_val(lists[num_lists - 1], list_sizes[num_lists - 1], val) +
        count_total_val(lists, list_sizes, num_lists - 1, val);
  }
*/

/*@
  requires num_lists >= 0;
  requires \valid_read_array(list_sizes, num_lists);
  requires \valid_read_array(lists, num_lists);
  requires \forall integer i; 0 <= i < num_lists ==> list_sizes[i] >= 0;
  requires \forall integer i; 0 <= i < num_lists ==> \valid_read_array(lists[i], list_sizes[i]);
  requires \valid_write_array(frequencies, max_val + 1); // Ensure frequencies array is large enough
  requires max_val >= -1; // max_val can be -1 if no elements are present, or 0 if all are 0.
                          // If max_val is -1, frequencies[0]...frequencies[-1] is an empty range, which is fine.

  // Prevent overflow for frequency counts.
  // The maximum possible count for any element is the total number of elements.
  // max_elements = sum of all list_sizes[i].
  // Assuming list_sizes[i] and num_lists are int, max_elements could be large.
  // If sum of all list_sizes[i] exceeds INT_MAX, this function might not be able to store all counts.
  // We assume here that the total number of elements will not cause an overflow in the frequency counts.
  // For simplicity, we add a general overflow protection for the sum.
  // This is a heuristic; a more precise bound would require a sum_axiomatic.
  requires (\sum integer i; 0 <= i < num_lists; list_sizes[i]) <= INT_MAX;

  assigns frequencies[0..max_val]; // Assigns to the relevant part of the frequencies array

  ensures \forall integer val; 0 <= val <= max_val ==>
    frequencies[val] == count_total_val(lists, list_sizes, num_lists, val);
  ensures \forall integer val; val < 0 || val > max_val ==> \old(frequencies[val]) == frequencies[val];
*/
void calculate_frequencies(int** lists, int* list_sizes, int num_lists, int* frequencies, int max_val) {
    /*@
      loop invariant 0 <= i <= max_val;
      loop invariant \forall integer k; 0 <= k < i ==> frequencies[k] == 0;
      loop assigns frequencies[0..max_val];
      loop variant max_val - i;
    */
    for (int i = 0; i <= max_val; ++i) {
        frequencies[i] = 0;
    }

    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant \forall integer val; 0 <= val <= max_val ==>
        frequencies[val] == count_total_val(lists, list_sizes, i, val);
      loop assigns frequencies[0..max_val];
      loop variant num_lists - i;
    */
    for (int i = 0; i < num_lists; ++i) {
        int* current_list = lists[i];
        int current_list_size = list_sizes[i];

        /*@
          loop invariant 0 <= j <= current_list_size;
          loop invariant \forall integer val; 0 <= val <= max_val ==>
            frequencies[val] == count_total_val(lists, list_sizes, i, val) +
                                count_val(current_list, j, val);
          loop assigns frequencies[0..max_val];
          loop variant current_list_size - j;
        */
        for (int j = 0; j < current_list_size; ++j) {
            int element = current_list[j];
            /*@
              assert 0 <= element; // Assuming elements are non-negative for this frequency calculation
            */
            if (element <= max_val && element >= 0) {
                // Prevent overflow for frequencies[element]
                // This requires frequencies[element] < INT_MAX before increment.
                // This is covered by the requires clause on the function.
                frequencies[element]++;
            }
        }
    }
}
