// Task ID: 29
// Generation: 0

/*@
  // Axiomatic block for recursive logic and helper axioms (Rule II.1, II.2)
  axiomatic OddCount {
    logic integer odd_count_recursive{L}(int *a, integer start, integer end, int val) reads a[start..end];

    axiom odd_count_base{L}:
      \for_all int *a, integer val, integer start;
        odd_count_recursive(a, start, start, val) == (if a[start] == val then 1 else 0);

    axiom odd_count_recursive_step{L}:
      \for_all int *a, integer val, integer start, integer end;
        start < end ==>
        odd_count_recursive(a, start, end, val) == odd_count_recursive(a, start, end - 1, val) + (if a[end] == val then 1 else 0);

    // Helper axiom: The count of an element is non-negative
    axiom odd_count_non_negative{L}:
      \for_all int *a, integer val, integer start, integer end;
        start <= end ==>
        odd_count_recursive(a, start, end, val) >= 0;
  }
*/

/*@
  requires N > 0;
  requires \valid_read_range(a, 0, N - 1);
  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function returns 1 (true) if such an element is found, 0 (false) otherwise.
  ensures (\exists integer k; 0 <= k < N && odd_count_recursive(a, 0, N - 1, a[k]) % 2 == 1) <==> (\result == 1);
  ensures (\result == 1) ==> (\exists integer k; 0 <= k < N && odd_count_recursive(a, 0, N - 1, a[k]) % 2 == 1);
  ensures (\result == 0) ==> (\forall integer k; 0 <= k < N ==> odd_count_recursive(a, 0, N - 1, a[k]) % 2 == 0);
*/
int find_odd_occurrence(int *a, int N) {
  /*@
    loop invariant 0 <= i <= N;
    loop invariant \forall integer k; 0 <= k < i ==> odd_count_recursive(a, 0, N - 1, a[k]) % 2 == 0;
    loop assigns i;
    loop variant N - i;
  */
  for (int i = 0; i < N; i++) {
    int current_element = a[i];
    int count = 0;

    /*@
      loop invariant 0 <= j <= N;
      loop invariant \forall integer k; 0 <= k < j && a[k] == current_element ==> \at(count, LoopEntry) + odd_count_recursive(a, 0, j-1, current_element) == count;
      loop invariant \forall integer k; j <= k < N && a[k] == current_element ==> current_element == a[k]; // Maintain identity
      loop assigns count, j;
      loop variant N - j;
    */
    for (int j = 0; j < N; j++) {
      if (a[j] == current_element) {
        count++;
      }
    }

    if (count % 2 == 1) {
      return 1; // Found an element with odd count
    }
  }

  return 0; // No element found with odd count
}
