// Task ID: 19
// Generation: 6

/*@
  // Rule I.1: No standard libraries, use built-in constants if needed.
  // We need to define `INT_MAX` for the ensures clause.
  // It's implicitly available in Frama-C's logic.

  // Rule II.1: Recursive logic for complex properties.
  // Axiomatic block to define properties of arrays.
  axiomatic ArrayProperties {
    logic boolean contains_duplicates_logic{L}(int* arr, int size) reads arr[0..size-1];

    axiom contains_duplicates_base{L}:
      \forall int* arr, integer size;
        size <= 1 ==> !contains_duplicates_logic(arr, size);

    axiom contains_duplicates_recursive_found{L}:
      \forall int* arr, integer size;
        size > 1 && (\exists integer k; 0 <= k < size - 1 && arr[k] == arr[size-1]) ==>
          contains_duplicates_logic(arr, size);

    axiom contains_duplicates_recursive_not_found{L}:
      \forall int* arr, integer size;
        size > 1 && (\forall integer k; 0 <= k < size - 1 ==> arr[k] != arr[size-1]) ==>
          (contains_duplicates_logic(arr, size) <==> contains_duplicates_logic(arr, size-1));

    // Rule II.2: Helper axioms for recursive functions.
    // This helper axiom links the logic function to the existence of duplicates.
    axiom contains_duplicates_exists{L}:
      \forall int* arr, integer size;
        contains_duplicates_logic(arr, size) <==>
          (\exists integer i, j; 0 <= i < j < size && arr[i] == arr[j]);
  }
*/

/*@
  requires size >= 0;
  // Rule II.5: Prevent RTE. Accessing arr[0..size-1] requires size to be valid.
  // The reads clause implicitly handles this for non-null array.
  requires \valid_read_range(arr, 0, size - 1);

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  ensures contains_duplicates_logic(arr, size) <==> (\result == 1);
*/
int containsDuplicate(int* arr, int size) { // Rule I.2: Use int for booleans.
    /*@
      loop invariant 0 <= i <= size;
      loop invariant \forall integer k; 0 <= k < i ==>
        (\forall integer l; k < l < size ==> arr[k] != arr[l]); // No duplicates from arr[k] to the end

      loop assigns i, j; // Variables modified within the outer loop body.
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        /*@
          loop invariant i < j <= size;
          loop invariant \forall integer k; i < k < j ==> arr[i] != arr[k];

          loop assigns j;
          loop variant size - j;
        */
        for (int j = i + 1; j < size; j++) {
            if (arr[i] == arr[j]) {
                return 1; // Duplicate found.
            }
        }
    }
    return 0; // No duplicates found.
}
