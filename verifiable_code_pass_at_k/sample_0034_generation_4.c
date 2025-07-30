// Task ID: 34
// Generation: 4

/*@
  // Rule II.1, II.2: Define recursive logic for properties over sequences.
  // This axiomatic block defines what it means for an array to contain
  // numbers from a specific range with one missing.
  axiomatic MissingNumber {
    logic integer sum_range(integer low, integer high) =
      if low > high then 0
      else low + sum_range(low + 1, high);

    // Rule II.2: Helper axiom to prove properties of sum_range.
    // This is a common formula for sum of an arithmetic progression.
    axiom sum_range_formula:
      orall integer low, high;
        low <= high ==> sum_range(low, high) == (high - low + 1) * (low + high) / 2;
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent potential overflow if n is very large.
  // The sum of numbers up to n+1 can exceed INT_MAX.
  // For (n+1)*(n+2)/2 to fit in int, (n+1)*(n+2) must fit in 2*INT_MAX.
  // Max n for sum_range to fit in int:
  // If INT_MAX is 2,147,483,647, then (n+1)*(n+2) must be <= 4,294,967,294.
  // n+1 approx sqrt(4.29e9) = 65535.
  // So, n approx 65534.
  requires n <= 65534; // Max n such that sum of 1 to n+1 fits in int.

  // The array must be sorted and contain distinct elements.
  requires orall integer i; 0 <= i < n - 1 ==> a[i] < a[i+1];
  // The array elements must be positive.
  requires orall integer i; 0 <= i < n ==> a[i] >= 1;
  // The array elements must be within the expected range, i.e., at most n+1.
  requires orall integer i; 0 <= i < n ==> a[i] <= n + 1;

  // The array must contain exactly n distinct numbers, which are a subset
  // of {1, ..., n+1} with one element missing.
  // This implies the sum of elements in 'a' is (sum of 1 to n+1) - missing_number.
  // And the missing number is between 1 and n+1.

  assigns 
othing;

  // The result is the missing number.
  // The sum of numbers from 1 to n+1 minus the sum of numbers in the array 'a'
  // should yield the missing number.
  // The sum of elements in 'a' is sum_range(0, n-1) using the array index.
  // To avoid recomputing sum of array elements, we can express the ensures clause
  // as the property that the result is the unique number in the range [1, n+1]
  // that is not present in the array.
  ensures 1 <= result <= n + 1;
  ensures (\exists integer k; 0 <= k < n && a[k] == result) <==> (result == 0); // This should be false.
  // The result is not in the array.
  ensures orall integer k; 0 <= k < n ==> a[k] != result;
  // All other numbers in the range [1, n+1] are in the array.
  ensures orall integer val; 1 <= val <= n + 1 && val != result ==> (\exists integer k; 0 <= k < n && a[k] == val);

  // Alternative ensures clause using sum (more direct to the common algorithm):
  // ensures result == sum_range(1, n + 1) - (\sum integer i; 0 <= i < n; a[i]);
*/
int find_missing_number(int* a, int n) { // Rule I.3: int* for array parameter.
    // Calculate the expected sum of numbers from 1 to n+1.
    // This sum can be (n+1)*(n+2)/2.
    // We use long long for intermediate calculation to prevent overflow before division,
    // although the requires clause should ensure final result fits int.
    long long expected_sum_ll = (long long)(n + 1) * (n + 2) / 2;
    int expected_sum = (int)expected_sum_ll;

    int actual_sum = 0;
    /*@
      loop invariant 0 <= i <= n;
      loop invariant actual_sum == (\sum integer k; 0 <= k < i; a[k]);
      loop assigns i, actual_sum;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        actual_sum += a[i];
    }

    return expected_sum - actual_sum;
}
