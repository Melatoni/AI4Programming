// Task ID: 34
// Generation: 6

/*@
  // Rule II.1: Define an axiomatic block for recursive logic.
  // This axiomatic block defines the property of a sorted array
  // and the sum of elements, which can be useful for verification.
  axiomatic ArrayProperties {
    // Rule I.3: Array parameters decay to pointers.
    logic boolean is_sorted{L}(int* a, int n) =
      \forall integer i; 0 <= i < n - 1 ==> a[i] <= a[i+1];

    // Rule II.1: Recursive logic for sum.
    logic integer sum_array{L}(int* a, int n) =
      if n <= 0 then 0
      else sum_array(a, n - 1) + a[n-1];

    // Helper axiom for sum of an arithmetic progression 0 to N.
    // This is the sum of the expected complete sequence.
    axiom sum_0_to_N:
      \forall integer N; N >= 0 ==> sum_array_expected(N) == N * (N + 1) / 2;

    // Recursive logic for the sum of expected numbers from 0 to N.
    logic integer sum_array_expected(integer N) =
      if N <= 0 then 0
      else sum_array_expected(N-1) + N;

    // Helper axiom: If an array is sorted and elements are distinct,
    // then a[i] == a[0] + i if a[0] is 0.
    // This axiom is specific to the problem interpretation (0 to N sequence).
    axiom distinct_sorted_elements_from_zero:
      \forall int* a, integer n;
        n > 0 && is_sorted(a, n) && a[0] == 0 &&
        (\forall integer i; 0 <= i < n - 1 ==> a[i+1] == a[i] + 1) ==>
        (\forall integer i; 0 <= i < n ==> a[i] == i);
  }
*/

/*@
  requires n > 0; // Array must have at least one element.
  requires \valid_read_array(arr, n); // Array must be readable for n elements.
  requires is_sorted(arr, n); // The array must be sorted.
  // The problem implies distinct consecutive integers with one missing.
  // This means the range of numbers is from 0 to n (inclusive),
  // and the array contains n distinct numbers from this range.
  // So, the smallest element must be 0 and the largest at most n.
  requires arr[0] == 0;
  requires arr[n-1] <= n;
  // All elements are non-negative.
  requires \forall integer i; 0 <= i < n ==> arr[i] >= 0;

  // Prevent overflow for sum_array_expected(n+1) and sum_array(arr, n)
  // The maximum sum for N numbers (0 to N) is N*(N+1)/2.
  // For 32-bit int, INT_MAX is 2,147,483,647.
  // N*(N+1)/2 <= INT_MAX => N*(N+1) <= 2*INT_MAX => N^2 approx 2*INT_MAX
  // N approx sqrt(2*INT_MAX) approx sqrt(4.29*10^9) approx 65535.
  // So, n (array length) must be significantly less than 65535.
  // Let's assume n+1 is the max value in sequence, so the sum is (n+1)*(n+2)/2.
  // If n is 46340, then n+1 is 46341, (n+1)*(n+2)/2 can overflow.
  // A safer upper bound for n for sum_array_expected(n+1) is around 65534.
  // Let's use 46340 as a conservative value to prevent overflow of (n+1)*(n+2)
  // before division by 2, assuming n+1 is the largest number in the sequence.
  requires n <= 46340; // To prevent overflow of sum_array_expected and the actual sum.

  assigns \nothing;

  // The missing number is the difference between the expected sum
  // (if all numbers from 0 to n were present) and the actual sum of the array.
  ensures \result == sum_array_expected(n) - sum_array(arr, n);
  // Alternative ensures clause using property:
  // ensures \result == (\sum integer i; 0 <= i <= n; i) - (\sum integer j; 0 <= j < n; arr[j]);
  // The sum in ACSL is not directly supported via \sum for proving,
  // so the recursive `sum_array` function is preferred.
  // Also, we can prove that the result is the number that is not in the array
  // but should be in the sequence 0 to n.
  ensures 0 <= \result <= n; // The missing number must be in the expected range.
  ensures (\forall integer k; 0 <= k < n ==> arr[k] != \result); // Result is not in array.
  ensures (\exists integer k; 0 <= k <= n && (\forall integer l; 0 <= l < n ==> arr[l] != k) && k == \result);
*/
int find_missing_number(int* arr, int n) {
    // The sum of numbers from 0 to n (inclusive) is n * (n + 1) / 2.
    // This is the sum if no number was missing.
    // The actual array contains n numbers. So the expected sum is for n+1 elements: 0 to n.
    long long expected_sum = (long long)n * (n + 1) / 2; // Use long long to avoid intermediate overflow for n=46340

    long long actual_sum = 0;
    /*@
      loop invariant 0 <= i <= n;
      loop invariant actual_sum == sum_array(arr, i);
      loop assigns i, actual_sum;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        actual_sum += arr[i];
    }

    return (int)(expected_sum - actual_sum);
}

/*@
  requires n > 0;
  requires \valid_read_array(arr, n);
  requires is_sorted(arr, n);
  requires arr[0] == 0;
  requires arr[n-1] <= n;
  requires \forall integer i; 0 <= i < n ==> arr[i] >= 0;
  requires n <= 46340;

  assigns \nothing;

  // This function implements the alternative approach: iterate and check
  // if arr[i] is equal to i. The first mismatch is the missing number.
  // This approach is typically more efficient and robust for sorted arrays
  // (doesn't rely on sum which can overflow for large N).
  ensures \result == (\exists integer i; 0 <= i < n && arr[i] != i ? i : (if (\forall integer k; 0 <= k < n ==> arr[k] == k) then n else -1));
  // The ensures clause for this function is more complex as it needs to capture
  // the 'first mismatch' or 'n' if no mismatch.
  // Let's refine it:
  // If there's an i such that arr[i] != i, then the result is the smallest such i.
  // If arr[i] == i for all i from 0 to n-1, then the missing number is n.
  ensures (\exists integer k; 0 <= k <= n && (\forall integer l; 0 <= l < n ==> arr[l] != k) && k == \result);
  ensures 0 <= \result <= n;
  ensures (\forall integer k; 0 <= k < n ==> arr[k] != \result);
*/
int find_missing_number_iterative(int* arr, int n) {
    /*@
      loop invariant 0 <= i <= n;
      // Invariant: For all k < i, arr[k] == k.
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] == k;
      loop assigns i;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (arr[i] != i) {
            return i;
        }
    }
    // If the loop completes, it means arr[i] == i for all i from 0 to n-1.
    // In this case, the missing number is n.
    return n;
}
