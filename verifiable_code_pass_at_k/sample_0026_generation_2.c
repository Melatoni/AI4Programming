// Task ID: 26
// Generation: 2

/*@
  // Rule II.1: Define recursive logic for sum and existence within an axiomatic block.
  axiomatic TupleList {
    logic integer get_count_of_k(int k, int* arr, int size);
    
    // Base case: empty array
    axiom get_count_of_k_base:
      \forall int k, int* arr; get_count_of_k(k, arr, 0) == 0;
    
    // Recursive case: if current element is k, add 1, otherwise add 0.
    axiom get_count_of_k_rec:
      \forall int k, int* arr, int size;
      size > 0 ==> get_count_of_k(k, arr, size) ==
        (if arr[size - 1] == k then 1 else 0) + get_count_of_k(k, arr, size - 1);
    
    // Rule II.2: Helper axiom to prove that if all elements are k, count is size.
    axiom get_count_of_k_all_k:
      \forall int k, int* arr, int size;
      (\forall integer i; 0 <= i < size ==> arr[i] == k) ==> get_count_of_k(k, arr, size) == size;

    // Rule II.2: Helper axiom to prove that if count is size, all elements are k.
    axiom get_count_of_k_is_size_implies_all_k:
      \forall int k, int* arr, int size;
      get_count_of_k(k, arr, size) == size ==> (\forall integer i; 0 <= i < size ==> arr[i] == k);
  }
*/

/*@
  requires size >= 0;
  requires \valid_read(arr + (0..size - 1));
  
  assigns \nothing;
  
  // Rule II.3: Use logical equivalence for boolean-like return values.
  ensures (get_count_of_k(k, arr, size) == size) <==> (esult == 1);
*/
int has_all_k_elements(int k, int* arr, int size) {
    /*@
      loop invariant 0 <= i <= size;
      // The count of 'k' elements found so far matches the recursive definition for the processed prefix.
      loop invariant get_count_of_k(k, arr, i) == \at(get_count_of_k(k, arr, i), LoopEntry); // This helps WP connect with the axiomatic definition.
      // If we found a non-k element, we should have already returned 0.
      loop invariant \forall integer j; 0 <= j < i ==> arr[j] == k;
      
      loop assigns i;
      loop variant size - i;
    */
    for (int i = 0; i < size; ++i) {
        if (arr[i] != k) {
            return 0; // Found an element not equal to k.
        }
    }
    return 1; // All elements were k.
}
