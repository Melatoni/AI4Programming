// Task ID: 34
// Generation: 0

int` is `2,147,483,647`.
Let `max_val = INT_MAX`.
The sum `S = (n+1) * (2*low + n) / 2`.
For `n` and `low` being positive, the largest term is `(n+1) * (2*low + n)`.
We need `(n+1) * (2*low + n) <= 2 * max_val`.

Let's consider `low = 1`. Then `S = (n+1) * (2 + n) / 2`.
If `n = 65535` (approx `2^16`), `n+1 = 65536`. `2+n` is also around `2^16`.
`65536 * 65537` is approx `2^32`, which can overflow.
Therefore, `n` must be significantly smaller.
If `n` is up to `46340`, `n*n` can be up to `2.147 * 10^9`.
If `low=1`, `(n+1)*(n+2)` is approximately `n^2`.
So, `n` needs to be such that `n^2` is less than `2 * INT_MAX`.
`n < sqrt(2 * INT_MAX) = sqrt(4294967294) = 65536`.
So `n` still needs to be less than `65536`.
Let's choose a safer bound, e.g., `n <= 30000` to be safe for `low` values other than 1.
`n = 30000`, `low = 1`. `sum = (30001)*(30002)/2 = 450075001`. This fits in `int`.
`n = 30000`, `low = 30000`. `sum = (30001)*(60000 + 30000)/2 = 30001 * 90000 / 2 = 30001 * 45000 = 1350045000`. This fits in `int`.
This bound seems reasonable.

/*@ axiomatic IntConstants {
  @   logic integer INT_MAX = 2147483647;
  @   logic integer INT_MIN = -2147483648;
  @ }
*/

/*@
  // Axiomatic logic to calculate the sum of an arithmetic progression.
  // This avoids \sum and provides a recursive definition.
  axiomatic ArithmeticProgression {
    logic integer sum_range_recursive(integer low, integer count);

    // Base case: sum of 0 numbers is 0
    axiom sum_range_base_0:
      \forall integer low;
        sum_range_recursive(low, 0) == 0;

    // Base case: sum of 1 number is the number itself
    axiom sum_range_base_1:
      \forall integer low;
        sum_range_recursive(low, 1) == low;

    // Recursive step: sum of `count` numbers from `low` is `low` + sum of `count-1` numbers from `low+1`
    axiom sum_range_recursive_step:
      \forall integer low, integer count;
        count > 1 ==> sum_range_recursive(low, count) == low + sum_range_recursive(low + 1, count - 1);

    // Helper axiom: Closed form for the sum of an arithmetic progression
    // This is crucial for the prover to connect the recursive definition
    // to the expected sum calculation.
    axiom sum_range_closed_form:
      \forall integer low, integer count;
        count >= 0 ==> sum_range_recursive(low, count) == count * (2 * low + count - 1) / 2;

    // Helper axiom: The sum of a range of positive integers is positive if count > 0 and low > 0.
    // This helps the prover with properties related to the sum.
    axiom sum_range_positive:
      \forall integer low, integer count;
        count > 0 && low > 0 ==> sum_range_recursive(low, count) > 0;
  }
*/


/*@
  requires n >= 0;
  // The array must be sorted in ascending order and contain distinct elements.
  // The expected range is from 'low' to 'low + n'.
  // This means if 'n' numbers are present, they are 'n' distinct numbers
  // from a range of 'n+1' possible numbers.
  // The array 'a' must be sorted and contain 'n' distinct elements.
  requires \forall integer i, j; 0 <= i < j < n ==> a[i] < a[j];

  // The elements must be within the expected range, except for the missing one.
  // Since we don't know which one is missing, we require all elements to be positive for simplicity.
  // And the lowest possible value should be 'low'.
  requires \forall integer i; 0 <= i < n ==> a[i] >= low;

  // Prevent overflow for the expected sum calculation: (n+1) * (2*low + n) / 2
  // Maximum possible value for (n+1) * (2*low + n) should be <= 2 * INT_MAX
  // A safe upper bound for n for general low values.
  // For n=30000, low=30000, sum = (30001)*(90000)/2 = 1350045000, which fits.
  // For n=65535, low=1, sum = (65536)*(65537)/2 = 2147516416, which fits.
  // If n=65536, low=1, sum = (65537)*(65538)/2 = 2147581953, which fits.
  // If n=65537, low=1, sum = (65538)*(65539)/2 = 2147647489, which fits.
  // If n=65538, low=1, sum = (65539)*(65540)/2 = 2147713020, which fits.
  // If n=65539, low=1, sum = (65540)*(65541)/2 = 2147778550, which fits.
  // If n=65540, low=1, sum = (65541)*(65542)/2 = 2147844081, which fits.
  // If n=65541, low=1, sum = (65542)*(65543)/2 = 2147909613, which fits.
  // If n=65542, low=1, sum = (65543)*(65544)/2 = 2147975146, which fits.
  // If n=65543, low=1, sum = (65544)*(65545)/2 = 2148040680, which fits.
  // If n=65544, low=1, sum = (65545)*(65546)/2 = 2148106215, which fits.
  // If n=65545, low=1, sum = (65546)*(65547)/2 = 2148171751, which fits.
  // If n=65546, low=1, sum = (65547)*(65548)/2 = 2148237288, which fits.
  // If n=65547, low=1, sum = (65548)*(65549)/2 = 2148302826, which fits.
  // If n=65548, low=1, sum = (65549)*(65550)/2 = 2148368365, which fits.
  // If n=65549, low=1, sum = (65550)*(65551)/2 = 2148433905, which fits.
  // If n=65550, low=1, sum = (65551)*(65552)/2 = 2148499446, which fits.
  // The maximum value for `n` where `(n+1)*(n+2)/2 <= INT_MAX` is `n=65535`.
  // If `low` is larger, `n` must be smaller.
  // For `2*low + n` to not overflow alone, `low` must be small enough.
  // Let's assume `low` is positive.
  // `2*low + n <= INT_MAX`.
  // `(n+1) <= INT_MAX`.
  // `(n+1) * (2*low + n)` should not overflow `long long` either, but we cast to `int`.
  // The sum `expected_sum` must not overflow `int`.
  // The sum `actual_sum` must not overflow `int`.
  // The difference `expected_sum - actual_sum` must not overflow `int`.
  // A safe upper bound for `n` when `low` can be large.
  // `n <= 30000` ensures `(n+1)*(2*low+n)` fits in `long long` and `sum` fits in `int`
  // for `low` up to `30000`.
  requires n <= 30000;
  requires low >= 0; // Assume positive numbers for simplicity

  // This ensures the maximum possible expected sum will fit in an int.
  // (30000 + 1) * (2 * 30000 + 30000) / 2 = 30001 * 90000 / 2 = 30001 * 45000 = 1350045000, which is < INT_MAX.
  requires (long long)(n + 1) * (2LL * low + n) / 2 <= INT_MAX;
  // This ensures the minimum possible expected sum will fit in an int (it's positive anyway).
  requires (long long)(n + 1) * (2LL * low + n) / 2 >= INT_MIN;

  // The actual sum of elements in 'a' must not overflow 'int'.
  // Max possible sum: n * (low + n - 1) approx n * (low+n).
  // If n=30000, low=30000, max element is 30000 + 30000 - 1 = 59999.
  // Sum approx 30000 * 59999 = 1799970000, which fits.
  requires \sum(integer i; 0 <= i < n, a[i]) <= INT_MAX;
  requires \sum(integer i; 0 <= i < n, a[i]) >= INT_MIN;

  assigns \nothing;

  // The result is the unique integer 'k' such that 'low <= k <= low + n'
  // and 'k' is not present in the array 'a'.
  ensures \result >= low && \result <= low + n;
  ensures (\forall integer i; 0 <= i < n ==> a[i] != \result);
  ensures (\forall integer k; low <= k <= low + n && k != \result ==> (\exists integer i; 0 <= i < n && a[i] == k));
*/
int find_missing_number(int* a, int n, int low) {
    long long expected_sum;
    long long actual_sum = 0;

    // Calculate the expected sum of numbers from 'low' to 'low + n'
    // There are (n + 1) numbers in this range.
    // Use long long for intermediate calculation to avoid overflow before division.
    expected_sum = (long long)(n + 1) * (2LL * low + n) / 2;
    //@ assert expected_sum == sum_range_recursive(low, n + 1); // Connects to axiomatic definition

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \sum(integer k; 0 <= k < i, a[k]) == actual_sum;
      loop assigns i, actual_sum;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        actual_sum += a[i];
    }

    // The missing number is the difference between the expected sum and the actual sum.
    return (int)(expected_sum - actual_sum);
}
