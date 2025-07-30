// Task ID: 34
// Generation: 2

/*@
  // Rule II.1: Define recursive logic for array properties.
  axiomatic ArrayProperties {
    logic integer array_value(int* a, integer idx);

    axiom array_value_def{L}:
      \forall int* a, integer idx; array_value(a, idx) == a[idx];

    // Rule II.1, II.2: Recursive logic to check if array is sorted.
    logic boolean is_sorted_segment(int* a, integer low, integer high);

    axiom is_sorted_segment_base:
      \forall int* a, integer low; is_sorted_segment(a, low, low);

    axiom is_sorted_segment_recursive:
      \forall int* a, integer low, integer high;
        low < high ==> is_sorted_segment(a, low, high) <==>
          (a[low] < a[low+1] && is_sorted_segment(a, low+1, high));

    // Rule II.1, II.2: Recursive logic to check if all elements are consecutive.
    logic boolean is_consecutive_segment(int* a, integer low, integer high);

    axiom is_consecutive_segment_base:
      \forall int* a, integer low; is_consecutive_segment(a, low, low);

    axiom is_consecutive_segment_recursive:
      \forall int* a, integer low, integer high;
        low < high ==> is_consecutive_segment(a, low, high) <==>
          (a[low+1] == a[low] + 1 && is_consecutive_segment(a, low+1, high));

    // Rule II.1, II.2: Recursive logic to check if all elements are positive.
    logic boolean all_positive_segment(int* a, integer low, integer high);

    axiom all_positive_segment_base:
      \forall int* a, integer low; all_positive_segment(a, low, low) <==> (a[low] > 0);

    axiom all_positive_segment_recursive:
      \forall int* a, integer low, integer high;
        low < high ==> all_positive_segment(a, low, high) <==>
          (a[low] > 0 && all_positive_segment(a, low+1, high));

    // Rule II.1, II.2: Recursive logic to check if all elements are non-negative.
    logic boolean all_non_negative_segment(int* a, integer low, integer high);

    axiom all_non_negative_segment_base:
      \forall int* a, integer low; all_non_negative_segment(a, low, low) <==> (a[low] >= 0);

    axiom all_non_negative_segment_recursive:
      \forall int* a, integer low, integer high;
        low < high ==> all_non_negative_segment(a, low, high) <==>
          (a[low] >= 0 && all_non_negative_segment(a, low+1, high));

    // Helper axiom: if a segment is consecutive, it's also sorted.
    axiom consecutive_implies_sorted:
      \forall int* a, integer low, integer high;
        is_consecutive_segment(a, low, high) ==> is_sorted_segment(a, low, high);
  }
*/

/*@
  requires N > 0;
  requires \valid_read(arr + (0..N-1));
  requires arr[0] > 0; // The problem implies positive numbers starting from 1.
  requires N < INT_MAX; // Prevent N from causing issues with loop bounds.
  // The array contains consecutive integers from arr[0] up to arr[N-1] + M, where M is the missing number.
  // The expected range of numbers is [arr[0], arr[0] + N].
  // So, the array should be arr[0], arr[0]+1, ..., arr[k], arr[k]+2, ..., arr[0]+N.
  // This means the array is sorted and contains distinct positive integers.
  requires is_sorted_segment(arr, 0, N-1);
  requires all_positive_segment(arr, 0, N-1);

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The result is the missing number if one exists.
  // If no number is missing, the result is arr[N-1] + 1 (the next expected number).
  ensures \result == arr[N-1] + 1 ||
          (\exists integer k; 0 <= k < N-1 && \result == arr[k] + 1 && arr[k+1] == arr[k] + 2 &&
                               (\forall integer i; 0 <= i <= k ==> arr[i] == arr[0] + i) &&
                               (\forall integer i; k+1 <= i < N ==> arr[i] == arr[0] + i + 1)
          );
  // This ensures that either the array is perfectly consecutive and the result is the 'next' number,
  // OR there is exactly one gap, and the result is the number that fills that gap.
  // It also implies that the numbers before the gap are consecutive from the start,
  // and numbers after the gap are consecutive from the number after the gap.

  // Alternative for the ensures clause (simpler, but might require more proof effort for specific properties):
  // ensures \result >= arr[0] && \result <= arr[0] + N;
  // ensures (\exists integer k; 0 <= k < N && arr[k] != arr[0] + k) ==> (\result == arr[0] + k);
  // ensures (\forall integer k; 0 <= k < N ==> arr[k] == arr[0] + k) ==> (\result == arr[N-1] + 1);

*/
int find_missing_number(int* arr, int N) {
    /*@
      loop invariant 0 <= i <= N;
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] == arr[0] + k;
      loop invariant i == N || (arr[i] != arr[0] + i); // If loop terminates early, arr[i] is the first mismatch.
      loop assigns i;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        if (arr[i] != arr[0] + i) {
            return arr[0] + i;
        }
    }
    // If the loop completes, it means all numbers from arr[0] to arr[N-1] are consecutive.
    // The missing number is then the next expected number.
    return arr[N-1] + 1;
}
