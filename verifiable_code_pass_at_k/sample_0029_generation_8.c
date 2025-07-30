// Task ID: 29
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.

  axiomatic OddOccurrences {
    logic integer count_occurrences(int* arr, int size, int val);

    // Base case: empty array or value not found.
    axiom count_occurrences_base_empty:
      \forall int* arr, int val;
        count_occurrences(arr, 0, val) == 0;

    // Recursive step: check first element and recurse on the rest.
    axiom count_occurrences_recursive:
      \forall int* arr, int size, int val;
        size > 0 ==>
        count_occurrences(arr, size, val) ==
        (if arr[0] == val then 1 else 0) + count_occurrences(arr + 1, size - 1, val);

    // Helper axiom: If an element is found, its count is at least 1.
    axiom count_occurrences_positive:
      \forall int* arr, int size, int val, integer i;
        0 <= i < size && arr[i] == val ==>
        count_occurrences(arr, size, val) >= 1;

    // Helper axiom: The count of an element is non-negative.
    axiom count_occurrences_non_negative:
      \forall int* arr, int size, int val;
        count_occurrences(arr, size, val) >= 0;

    // Helper axiom: The count is less than or equal to the size of the array.
    axiom count_occurrences_upper_bound:
      \forall int* arr, int size, int val;
        count_occurrences(arr, size, val) <= size;
  }
*/

/*@
  requires size >= 0; // The array can be empty.
  requires \valid_read_range(arr, 0, size - 1); // Array elements must be readable.

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like return.
  ensures (\exists integer i; 0 <= i < size && count_occurrences(arr, size, arr[i]) % 2 == 1) <==> (\result != -1);
  ensures \result == -1 || (0 <= \result < size && count_occurrences(arr, size, arr[\result]) % 2 == 1);
  ensures \result != -1 ==> (\forall integer k; 0 <= k < size && k != \result ==> count_occurrences(arr, size, arr[k]) % 2 == 0);
*/
int find_odd_occurrence(int* arr, int size) {
    /*@
      loop invariant 0 <= i <= size;
      loop invariant \forall integer k; 0 <= k < i ==> count_occurrences(arr, size, arr[k]) % 2 == 0;
      loop assigns i;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        int current_element = arr[i];
        int count = 0;

        /*@
          loop invariant 0 <= j <= size;
          loop invariant count == count_occurrences(arr, j, current_element);
          loop assigns j, count;
          loop variant size - j;
        */
        for (int j = 0; j < size; j++) {
            if (arr[j] == current_element) {
                count++;
            }
        }

        if (count % 2 == 1) {
            return i; // Return the index of an element with an odd count.
        }
    }

    return -1; // No element found with an odd number of occurrences.
}
