// Task ID: 34
// Generation: 7

int`, we need to constrain `n`. The maximum sum for 32-bit `int` is about `2*10^9`. `N*(N+1)/2` should not exceed `INT_MAX`. If `N` is roughly `65535`, `N*(N+1)/2` is about `2*10^9`. So, `n+1` should be less than or equal to `65535`. Thus, `n` should be less than or equal to `65534`.

/*@
  requires n >= 0;
  // Constraint to prevent overflow for sum calculations.
  // (n + 1) * (n + 2) / 2 must fit in int.
  // Max n for (n+1)*(n+2)/2 to fit in signed 32-bit int is n=65534.
  // 65535 * 65536 / 2 = 2147450880, which is < INT_MAX (2147483647).
  requires n <= 65534;

  // The array 'a' must be valid for reading 'n' elements.
  requires \valid_read(a + (0..n-1));

  // The array elements must be sorted and distinct.
  // Also, each element must be positive.
  // And the minimum value is 1.
  requires \forall integer k; 0 <= k < n ==> a[k] >= 1;
  requires \forall integer k; 0 <= k < n - 1 ==> a[k] < a[k+1];

  // The array must contain n numbers from the sequence 1, ..., n+1, with exactly one missing.
  // This means that for each expected number `i` from 1 to n+1, either it is present in `a`
  // or it is the single missing number.
  // More concretely, the first element must be 1 or 2, and the last element must be n or n+1.
  // And for any k, a[k] is either k+1 or k+2 (if an earlier number was missing).
  // This is a strong property for a sorted array with one missing element.
  // More simply: all elements in 'a' must be within the range [1, n+1].
  requires \forall integer k; 0 <= k < n ==> a[k] <= n + 1;

  assigns \nothing;

  // The ensures clause states that the result is the unique integer 'm'
  // such that 1 <= m <= n+1 and 'm' is not found in the array 'a'.
  ensures 1 <= \result <= n + 1;
  ensures \forall integer k; 0 <= k < n ==> a[k] != \result;
  ensures \forall integer m; 1 <= m <= n + 1 && m != \result ==> \exists integer k; 0 <= k < n && a[k] == m;
*/
int find_missing_number(int a[], int n) {
    long long expected_sum = (long long)(n + 1) * (n + 2) / 2;
    long long actual_sum = 0;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant 0 <= actual_sum <= expected_sum; // Sum should not exceed expected.
      // actual_sum is the sum of a[0]...a[i-1]
      loop invariant actual_sum == (\sum integer k; 0 <= k < i; a[k]);
      loop assigns i, actual_sum;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // Prevent overflow during summation.
        // The maximum value for a[i] is n+1. Max n is 65534.
        // So a[i] can be up to 65535.
        // actual_sum can be up to expected_sum (2147450880).
        // Adding a[i] to actual_sum could overflow if actual_sum is already near INT_MAX
        // and a[i] is large. However, actual_sum is `long long`, so this is fine.
        // We need to ensure that the final result `expected_sum - actual_sum` fits in `int`.
        // Since both `expected_sum` and `actual_sum` are `long long`, their difference
        // will also be `long long`. The `ensures` clause states `\result` is within `1..n+1`,
        // which will always fit in `int`. The cast at return is safe.
        actual_sum += a[i];
    }

    return (int)(expected_sum - actual_sum);
}
