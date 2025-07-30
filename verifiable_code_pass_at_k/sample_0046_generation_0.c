// Task ID: 46
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Define an axiomatic block for properties over arrays.
  axiomatic ArrayProperties {
    logic boolean is_distinct_from_rest(int *arr, int len, int index);

    // Axiom for the base case: an element is distinct from an empty rest of the array.
    axiom is_distinct_from_rest_base:
      \forall int *arr, int len, int index;
        index >= len ==> is_distinct_from_rest(arr, len, index);

    // Axiom for the recursive step: an element is distinct if it's not equal to the
    // current element and is distinct from the rest of the sub-array.
    axiom is_distinct_from_rest_recursive:
      \forall int *arr, int len, int index, int k;
        0 <= index < len && index <= k < len ==>
        (is_distinct_from_rest(arr, len, index) <==>
         (\forall int j; index < j < len ==> arr[index] != arr[j])
        );
  }

  // Rule II.5: Prevent Runtime Errors.
  // The function does not perform operations that typically lead to overflow
  // or division by zero with valid array inputs.
  // No specific 'requires' for value range is needed unless values are used in arithmetic.
  
  requires len >= 0; // Array length must be non-negative.
  requires \valid_read_array(arr, 0..len-1); // Ensure array is readable up to len-1.

  assigns \nothing; // The function only reads the array, does not modify it.

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  // The result is 1 if and only if all elements in the array are distinct.
  ensures (\forall integer i, j; 0 <= i < j < len ==> arr[i] != arr[j]) <==> (result == 1);
*/
int are_all_elements_distinct(int *arr, int len) {
    /*@
      loop invariant 0 <= i <= len;
      // Invariant: All elements from 0 to i-1 are distinct from each other.
      loop invariant \forall integer k1, k2; 0 <= k1 < k2 < i ==> arr[k1] != arr[k2];
      loop assigns i;
      // Rule II.4: Loop variant for termination.
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        /*@
          loop invariant i < j <= len;
          // Invariant: arr[i] is distinct from all elements arr[i+1]...arr[j-1].
          loop invariant \forall integer k; i < k < j ==> arr[i] != arr[k];
          loop assigns j;
          // Rule II.4: Loop variant for termination.
          loop variant len - j;
        */
        for (int j = i + 1; j < len; j++) {
            if (arr[i] == arr[j]) {
                return 0; // Found a duplicate, so not all elements are distinct.
            }
        }
    }
    return 1; // No duplicates found, all elements are distinct.
}
