// Task ID: 29
// Generation: 9

/*@ axiomatic OddOccurrence {
  logic integer count_occurrences{L}(int *a, integer start, integer end, int val);

  predicate is_odd(integer x) = x % 2 == 1;

  // Rule II.2: Base case for count_occurrences
  axiom count_occurrences_base_empty{L}:
    \forall int *a, integer start, end;
      start >= end ==> count_occurrences{L}(a, start, end, val) == 0;

  // Rule II.2: Recursive case for count_occurrences
  axiom count_occurrences_recursive{L}:
    \forall int *a, integer start, end, val;
      start < end ==>
        count_occurrences{L}(a, start, end, val) ==
          (if a[start] == val then 1 else 0) + count_occurrences{L}(a, start + 1, end, val);

  // Rule II.2, II.2.1: Helper axiom for count_occurrences
  // If an element appears an odd number of times in the full array,
  // and we split the array, it must appear an odd number of times in one part
  // and an even number of times in the other part.
  axiom count_occurrences_split{L}:
    \forall int *a, integer start, middle, end, val;
      start <= middle <= end ==>
        count_occurrences{L}(a, start, end, val) ==
          count_occurrences{L}(a, start, middle, val) + count_occurrences{L}(a, middle, end, val);
}
*/

/*@
  requires N > 0;
  requires \valid_read(A + (0..N-1));
  // All elements must be within the range of int to prevent overflow issues
  // if we were to use bitwise XORing, though this implementation does not.
  // This is a general safety constraint for array elements.
  requires \forall integer i; 0 <= i < N ==> A[i] >= INT_MIN && A[i] <= INT_MAX;

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence.
  // The result is the element 'x' such that its count in the array is odd.
  ensures (\exists integer x;
             is_odd(count_occurrences{Old}(A, 0, N, x)) &&
             (\forall integer y; y != x ==> !is_odd(count_occurrences{Old}(A, 0, N, y))))
          <==> (\result != INT_MIN -1); // INT_MIN -1 is an impossible value for valid int, used as a flag for "not found"
  // If the problem guarantees such an element exists, we can simplify:
  // ensures is_odd(count_occurrences{Old}(A, 0, N, \result));
*/
int find_odd_occurrence(int A[], int N) {
    /*@
      loop invariant 0 <= i <= N;
      loop invariant \forall integer k; 0 <= k < i ==>
        // Any element encountered so far (A[k]) has its count in A[0..k-1] and A[i..N-1] even,
        // or it's the odd one if it's the current 'current_xor_sum'.
        // This invariant is tricky to formalize directly with an `int` XOR sum.
        // A direct count-based approach is more robust for WP.
        // For XOR sum, the invariant is simpler: current_xor_sum is the XOR of A[0..i-1].
        current_xor_sum == (\xor integer j; 0 <= j < i; A[j]);
      loop assigns i, current_xor_sum;
      loop variant N - i;
    */
    int current_xor_sum = 0;
    for (int i = 0; i < N; i++) {
        current_xor_sum = current_xor_sum ^ A[i];
    }
    // If the problem guarantees that such an element exists,
    // then current_xor_sum will be that element.
    // If it's possible no such element exists (e.g., empty array or all even occurrences),
    // then the return value needs to signal that.
    // Given the problem statement "find the element occurring odd number of times",
    // it implies such an element exists and is unique (due to XOR properties).
    return current_xor_sum;
}
