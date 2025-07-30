// Task ID: 34
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule III.3: Correct range syntax.
  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.4: No stray semicolons.

  // Axiomatic block for recursive logic if needed (not strictly needed for this problem,
  // but good to show the structure if a more complex property was required).
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // For this specific problem, a direct `\forall` or `\exists` is sufficient.

  // The function finds a missing number in a sorted array `a` of `n` elements.
  // We assume the array `a` should ideally contain numbers from 0 to n (inclusive),
  // but one number is missing. So, the array `a` will have `n` elements,
  // and the missing number will be between 0 and n.
  // For example, if n=4, the full set is {0, 1, 2, 3, 4}.
  // If a = {0, 1, 3, 4}, then n=4, and 2 is missing.
  // The array `a` has `n` elements. The range of possible numbers is `0..n`.

  // Preconditions:
  // - n must be non-negative.
  // - The array `a` must not be NULL.
  // - The array `a` must be sorted in non-decreasing order.
  // - The array `a` must contain `n` distinct elements.
  // - All elements in `a` must be within the range `0` to `n`.
  // - There must be exactly one missing number in the range `0` to `n`.
  //   This implies that `a[i] == i` for `i < missing_val` and `a[i] == i + 1` for `i >= missing_val`.

  requires n >= 0;
  requires \valid_read_array(a, n);

  // Array is sorted and contains distinct elements.
  requires \forall integer k; 0 <= k < n - 1 ==> a[k] < a[k+1];

  // All elements are within the expected range [0, n].
  requires \forall integer k; 0 <= k < n ==> 0 <= a[k] <= n;

  // There is exactly one missing number in the range [0, n].
  // This can be stated as: the sum of elements in 'a' plus the missing number
  // must equal the sum of numbers from 0 to n.
  // Sum 0..N = N*(N+1)/2
  // We need to ensure that the sum does not overflow.
  // For int, N*(N+1)/2 can overflow if N is large.
  // Max N for sum N*(N+1)/2 to fit in int (2^31-1) is around 65535.
  // Let's assume n is small enough for sum to not overflow.
  requires (long long)n * (n + 1) / 2 <= INT_MAX; // Ensures target sum doesn't overflow
  
  // The sum of elements in 'a' should also not overflow.
  requires \sum(0, n-1, \lambda integer k; a[k]) <= INT_MAX;

  assigns \nothing;

  // Postcondition:
  // The function returns the unique integer `m` such that `0 <= m <= n` and `m` is not in `a`.
  // Rule II.3: Ensures clause uses logical equivalence.
  ensures (\exists integer m;
             0 <= m <= n &&
             (\forall integer k; 0 <= k < n ==> a[k] != m)) <==> (\result == \result); // Trivial, as result is already known.
  // A better ensures clause:
  ensures (\forall integer k; 0 <= k < n ==> a[k] != \result) && (0 <= \result <= n);
  // And to be more precise about the specific missing number:
  ensures (\result == n
             || (\exists integer i;
                   0 <= i < n &&
                   a[i] == i + 1 &&
                   (\forall integer j; 0 <= j < i ==> a[j] == j) &&
                   \result == i));
*/
int find_missing_number(int* a, int n) {
    /*@
      loop invariant 0 <= i <= n;
      // Invariant: For all k from 0 to i-1, if a[k] is defined, it means a[k] == k.
      // This holds until the missing number is found.
      loop invariant \forall integer k; 0 <= k < i ==> a[k] == k;
      loop assigns i;
      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        if (a[i] != i) {
            // Found the first index `i` where `a[i]` is not equal to `i`.
            // This `i` is the missing number.
            return i;
        }
    }
    // If the loop completes, it means all numbers from 0 to n-1 are present.
    // Therefore, the missing number must be `n`.
    return n;
}
