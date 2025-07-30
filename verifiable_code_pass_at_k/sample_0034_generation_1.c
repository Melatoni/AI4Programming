// Task ID: 34
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans (though not directly used in this problem).

  // Rule II.5: Prevent runtime errors.
  // The array size `n` must be non-negative.
  requires n >= 0;
  // If n is large, the sum `n * (n + 1) / 2` could overflow int.
  // For `int` (typically 32-bit signed), max value is 2,147,483,647.
  // `n * (n + 1) / 2 <= INT_MAX`
  // `n^2 approx 2 * INT_MAX`
  // `n approx sqrt(2 * INT_MAX) approx sqrt(4.29 * 10^9) approx 65536`.
  // So, n must be less than approx 65536 to prevent sum overflow.
  // Let's pick a safe upper bound.
  requires n <= 65535; // Maximum n for n*(n+1)/2 to fit in a signed 32-bit int.

  // The array `arr` must be valid and point to `n` elements.
  requires \valid_read(arr + (0..n-1));

  // The array must be sorted and contain distinct elements.
  // And the elements must be within the expected range [0, n].
  requires \forall integer k; 0 <= k < n ==> 0 <= arr[k] <= n;
  requires \forall integer k; 0 <= k < n-1 ==> arr[k] < arr[k+1];

  assigns \nothing;

  // Rule II.3: The ensures clause for boolean-like functions uses <==>.
  // But this function returns an integer, so a direct equivalence is not needed.
  // The result is the unique integer `m` such that `0 <= m <= n`
  // and `m` is not present in the array `arr`.
  ensures 0 <= \result <= n;
  ensures \forall integer k; 0 <= k < n ==> arr[k] != \result;
  ensures \forall integer v; 0 <= v <= n && v != \result ==> \exists integer k; 0 <= k < n && arr[k] == v;
*/
int find_missing_number(const int arr[], int n) { // Rule I.3: Array pointer decay.
    // The sum of numbers from 0 to n (inclusive) is n * (n + 1) / 2.
    // This is the sum of the sequence if no number were missing.
    int expected_sum = n * (n + 1) / 2;

    int actual_sum = 0;

    /*@
      // Rule II.4: Mandatory loop annotations.
      loop invariant 0 <= i <= n;
      // The actual_sum accumulates elements from arr[0] to arr[i-1].
      loop invariant actual_sum == (\sum integer k; 0 <= k < i; arr[k]);
      loop assigns i, actual_sum;
      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        actual_sum += arr[i];
    }

    // The missing number is the difference between the expected sum
    // and the actual sum of the array elements.
    return expected_sum - actual_sum;
}
