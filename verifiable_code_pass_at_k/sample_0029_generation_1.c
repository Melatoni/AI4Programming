// Task ID: 29
// Generation: 1

/*@
  // Axiomatic block for recursive logic (Rule II.1)
  axiomatic OddCount {
    logic integer count_occurrences{L}(int val, int* arr, integer from, integer to)
      reads arr[from..to];

    // Base case: empty range
    axiom count_occurrences_empty{L}:
      orall int val, int* arr, integer from, to;
        from > to ==> count_occurrences(val, arr, from, to) == 0;

    // Recursive case: single element
    axiom count_occurrences_single{L}:
      orall int val, int* arr, integer idx;
        count_occurrences(val, arr, idx, idx) == (arr[idx] == val ? 1 : 0);

    // Recursive case: split range
    axiom count_occurrences_recursive{L}:
      orall int val, int* arr, integer from, to;
        from <= to ==> count_occurrences(val, arr, from, to) ==
          (count_occurrences(val, arr, from, from) + count_occurrences(val, arr, from + 1, to));

    // Helper axiom for sum of odd/even numbers (Rule II.2)
    // If count is odd, then count + 1 (if val match) is even, and count + 0 (if val mismatch) is odd.
    // This helps the prover with parity.
    axiom count_occurrences_parity_match{L}:
      orall int val, int* arr, integer from, to;
        count_occurrences(val, arr, from, to) % 2 == 1 ==>
        (count_occurrences(val, arr, from, from) == 1 && count_occurrences(val, arr, from + 1, to) % 2 == 0) ||
        (count_occurrences(val, arr, from, from) == 0 && count_occurrences(val, arr, from + 1, to) % 2 == 1);

    axiom count_occurrences_parity_mismatch{L}:
      orall int val, int* arr, integer from, to;
        count_occurrences(val, arr, from, to) % 2 == 0 ==>
        (count_occurrences(val, arr, from, from) == 1 && count_occurrences(val, arr, from + 1, to) % 2 == 1) ||
        (count_occurrences(val, arr, from, from) == 0 && count_occurrences(val, arr, from + 1, to) % 2 == 0);
  }
*/

/*@
  requires N > 0;
  requires \valid_read_range(arr, 0, N - 1);
  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return.
  // The result is the element 'x' such that its count in 'arr' is odd.
  ensures (\exists integer x;
            (\exists integer i; 0 <= i < N && arr[i] == x) &&
            count_occurrences(x, arr, 0, N - 1) % 2 == 1 &&
            (\forall integer y; (y != x && (\exists integer j; 0 <= j < N && arr[j] == y)) ==> count_occurrences(y, arr, 0, N - 1) % 2 == 0)
          ) <==> ((\exists integer k; 0 <= k < N && result == arr[k]));

  // Additional ensures clause to specify the value of result if it exists.
  ensures ((\exists integer x;
            (\exists integer i; 0 <= i < N && arr[i] == x) &&
            count_occurrences(x, arr, 0, N - 1) % 2 == 1)
          ) ==>
          count_occurrences(result, arr, 0, N - 1) % 2 == 1;

  // The problem guarantees such an element exists for typical inputs,
  // but for formal verification, we must handle the case where it might not (e.g., all counts even).
  // However, the problem statement implies one will exist.
  // If no such element exists, behavior is undefined by the problem, but here we enforce result is some array element.
*/
int find_odd_occurrence(int* arr, int N) {
    int res = 0;
    /*@
      loop invariant 0 <= i <= N;
      // Invariant capturing that 'res' holds the XOR sum of elements encountered so far.
      // This works because XORing an element an even number of times results in 0,
      // and XORing it an odd number of times results in the element itself.
      loop invariant res == (\xor integer k; 0 <= k < i; arr[k]);
      loop assigns res, i;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        res = res ^ arr[i];
    }
    return res;
}
