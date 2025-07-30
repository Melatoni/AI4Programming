// Task ID: 40
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Define a maximum size for arrays to prevent overflow in declarations
  // and to provide a bound for logical functions.
  #define MAX_LIST_SIZE 100
  #define MAX_VALUE 1000

  // Axiomatic block for recursive logic to count occurrences of an element in a single list.
  axiomatic ListCount {
    logic integer count_in_list(int val, int* list, integer len);

    axiom count_in_list_empty:
      \forall int val, int* list;
        count_in_list(val, list, 0) == 0;

    axiom count_in_list_recursive:
      \forall int val, int* list, integer len;
        len > 0 ==> count_in_list(val, list, len) ==
          (if list[len - 1] == val then 1 else 0) + count_in_list(val, list, len - 1);

    // Rule II.2: Helper axiom for a common property.
    // Proves that if an element is not in the list, its count is 0.
    axiom count_in_list_not_present:
      \forall int val, int* list, integer len;
        (\forall integer i; 0 <= i < len ==> list[i] != val) ==> count_in_list(val, list, len) == 0;
  }

  // Axiomatic block for recursive logic to count occurrences of an element in a list of lists.
  axiomatic NestedListCount {
    logic integer count_in_nested_list(int val, int* nested_list_ptr, int* list_lengths, integer num_lists, integer max_col_size);

    axiom count_in_nested_list_empty:
      \forall int val, int* nested_list_ptr, int* list_lengths, integer max_col_size;
        count_in_nested_list(val, nested_list_ptr, list_lengths, 0, max_col_size) == 0;

    axiom count_in_nested_list_recursive:
      \forall int val, int* nested_list_ptr, int* list_lengths, integer num_lists, integer max_col_size;
        num_lists > 0 ==>
          count_in_nested_list(val, nested_list_ptr, list_lengths, num_lists, max_col_size) ==
            count_in_list(val, nested_list_ptr + (num_lists - 1) * max_col_size, list_lengths[num_lists - 1]) +
            count_in_nested_list(val, nested_list_ptr, list_lengths, num_lists - 1, max_col_size);

    // Helper axiom: if an element is not in any sublist, its total count is 0.
    axiom count_in_nested_list_not_present:
      \forall int val, int* nested_list_ptr, int* list_lengths, integer num_lists, integer max_col_size;
        (\forall integer i; 0 <= i < num_lists ==> count_in_list(val, nested_list_ptr + i * max_col_size, list_lengths[i]) == 0) ==>
          count_in_nested_list(val, nested_list_ptr, list_lengths, num_lists, max_col_size) == 0;
  }
*/

/*@
  requires num_lists >= 0;
  requires max_col_size > 0;
  requires \valid_read(nested_list_ptr + (0 .. num_lists * max_col_size - 1));
  requires \valid_read(list_lengths + (0 .. num_lists - 1));
  requires \forall integer i; 0 <= i < num_lists ==> 0 <= list_lengths[i] <= max_col_size;
  requires \valid_write(frequencies + (0 .. MAX_VALUE)); // Assuming elements are non-negative and less than MAX_VALUE

  // Rule II.5: Prevent RTE - ensure that elements are within valid range for frequency array.
  requires \forall integer i; 0 <= i < num_lists ==>
           \forall integer j; 0 <= j < list_lengths[i] ==>
             0 <= *(nested_list_ptr + i * max_col_size + j) < MAX_VALUE;

  assigns frequencies[0 .. MAX_VALUE];

  // Rule II.3: ensures clause using logical equivalence.
  // This ensures that each frequency[k] holds the correct total count of k.
  ensures \forall integer k; 0 <= k < MAX_VALUE ==>
            frequencies[k] == count_in_nested_list(k, nested_list_ptr, list_lengths, num_lists, max_col_size);
*/
void find_frequency(int* nested_list_ptr, int* list_lengths, int num_lists, int max_col_size, int* frequencies) {
    /*@
      loop invariant \forall integer k; 0 <= k < MAX_VALUE ==> frequencies[k] == 0;
      loop assigns frequencies[0 .. MAX_VALUE];
      loop variant MAX_VALUE - i;
    */
    for (int i = 0; i < MAX_VALUE; i++) {
        frequencies[i] = 0;
    }

    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant \forall integer k; 0 <= k < MAX_VALUE ==>
                       frequencies[k] == count_in_nested_list(k, nested_list_ptr, list_lengths, i, max_col_size);
      loop assigns i, frequencies[0 .. MAX_VALUE];
      loop variant num_lists - i;
    */
    for (int i = 0; i < num_lists; i++) {
        int current_list_len = list_lengths[i];
        int* current_list = nested_list_ptr + i * max_col_size;

        /*@
          loop invariant 0 <= j <= current_list_len;
          loop invariant \forall integer k; 0 <= k < MAX_VALUE ==>
                           frequencies[k] ==
                             count_in_nested_list(k, nested_list_ptr, list_lengths, i, max_col_size) +
                             count_in_list(k, current_list, j);
          loop assigns j, frequencies[0 .. MAX_VALUE];
          loop variant current_list_len - j;
        */
        for (int j = 0; j < current_list_len; j++) {
            int element = current_list[j];
            // Rule II.5: Ensure element is within bounds for array access
            /*@ assert 0 <= element < MAX_VALUE; */
            frequencies[element]++;
        }
    }
}
