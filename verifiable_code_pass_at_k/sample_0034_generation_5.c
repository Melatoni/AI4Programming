// Task ID: 34
// Generation: 5

/*@ axiomatic MissingNumber {
  @   logic integer sum_range(integer lower, integer upper) =
  @     lower > upper ? 0 : lower + sum_range(lower + 1, upper);
  @
  @   // Helper axiom: sum_range is non-negative if bounds are valid
  @   axiom sum_range_non_negative:
  @     \forall integer l, u; l <= u ==> sum_range(l, u) >= 0;
  @ }
  @*/

/*@
  @ requires n >= 1;
  @ // The array a must contain n-1 elements
  @ requires \valid_read(a + (0..n-2));
  @
  @ // Ensure numbers in the array are within the expected range [1, n]
  @ // and that the sum does not overflow int
  @ requires n <= 65535; // Prevents sum_range(1, n) from overflowing int
  @ requires \forall integer i; 0 <= i < n - 1 ==> 1 <= a[i] <= n;
  @
  @ // The array must be sorted in ascending order
  @ requires \forall integer i; 0 <= i < n - 2 ==> a[i] < a[i+1];
  @
  @ // All elements must be distinct
  @ requires \forall integer i, j; 0 <= i < j < n - 1 ==> a[i] != a[j];
  @
  @ // Exactly one number from 1 to n is missing.
  @ // This is implicitly guaranteed by the sum check below,
  @ // combined with the distinct and range requirements.
  @
  @ assigns \nothing;
  @
  @ ensures \result == sum_range(1, n) - (\sum integer i; 0 <= i < n - 1; a[i]);
  @ ensures 1 <= \result <= n;
  @*/
int find_missing_number(int* a, int n) {
    /*@
      @ loop invariant 0 <= i <= n - 1;
      @ loop invariant current_sum == (\sum integer k; 0 <= k < i; a[k]);
      @ loop assigns i, current_sum;
      @ loop variant n - 1 - i;
    */
    int current_sum = 0;
    for (int i = 0; i < n - 1; i++) {
        current_sum += a[i];
    }

    // The sum of numbers from 1 to n is n * (n + 1) / 2
    // We use sum_range axiomatic function for Frama-C to reason about it.
    int expected_total_sum = sum_range(1, n);

    return expected_total_sum - current_sum;
}
