// Task ID: 50
// Generation: 1

/*@
  // Axiomatic block for recursive logic and helper axioms (Rule II.1, II.2)
  axiomatic ListLength {
    logic integer list_length{L}(int* list, integer size);

    axiom list_length_empty{L}:
      \forall int* list, integer size;
        size == 0 ==> list_length(list, size) == 0;

    axiom list_length_recursive{L}:
      \forall int* list, integer size;
        size > 0 ==> list_length(list, size) == 1 + list_length(list + 1, size - 1);

    // Helper axiom for range of list_length (Rule II.2)
    axiom list_length_range{L}:
      \forall int* list, integer size;
        size >= 0 ==> list_length(list, size) == size;
  }
*/

/*@
  requires num_lists >= 0;
  requires \forall integer i; 0 <= i < num_lists ==> lists[i] != \null;
  requires \forall integer i; 0 <= i < num_lists ==> list_sizes[i] >= 0;

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence for boolean-like return
  ensures \result >= 0 && \result < num_lists;
  ensures \forall integer i; 0 <= i < num_lists ==> list_sizes[\result] <= list_sizes[i];
*/
int find_min_length_list_index(int** lists, int* list_sizes, int num_lists) {
  if (num_lists == 0) {
    return -1; // Or handle as an error, depending on specification. -1 indicates no list found.
  }

  int min_length = list_sizes[0];
  int min_index = 0;

  /*@
    loop invariant 0 <= i && i <= num_lists;
    loop invariant 0 <= min_index && min_index < i;
    loop invariant \forall integer k; 0 <= k < i ==> list_sizes[min_index] <= list_sizes[k];
    loop assigns i, min_length, min_index;
    loop variant num_lists - i;
  */
  for (int i = 1; i < num_lists; i++) {
    if (list_sizes[i] < min_length) {
      min_length = list_sizes[i];
      min_index = i;
    }
  }

  return min_index;
}
