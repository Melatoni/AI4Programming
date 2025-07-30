// Task ID: 42
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in formal parameters.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper axioms.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic RepeatedElements {
    // Defines whether an element at index 'idx' has been seen before 'idx'
    // in the array 'arr' up to 'limit'.
    logic boolean is_seen_before(int[] arr, int idx, int limit) =
      \exists integer k; 0 <= k < idx && k < limit && arr[k] == arr[idx];

    // Recursive logic to sum repeated elements.
    // base case: if start >= length, sum is 0.
    // recursive case: if arr[start] has been seen before (up to start), add arr[start].
    //                 otherwise, add 0.
    //                 Then recurse for start + 1.
    logic integer sum_repeated_elements_recursive(int[] arr, int start, int length)
      reads arr[0..length-1];

    axiom sum_repeated_elements_recursive_base{L}(int[] arr, int start, int length) =
      start >= length ==> sum_repeated_elements_recursive(arr, start, length) == 0;

    axiom sum_repeated_elements_recursive_step{L}(int[] arr, int start, int length) =
      start < length ==> sum_repeated_elements_recursive(arr, start, length) ==
        (if is_seen_before(arr, start, start) then arr[start] else 0) +
        sum_repeated_elements_recursive(arr, start + 1, length);

    // Helper axiom: if all elements are non-negative, the sum is non-negative.
    // This helps the prover with ranges.
    axiom sum_repeated_elements_non_negative{L}(int[] arr, int start, int length) =
      (\forall integer i; start <= i < length ==> arr[i] >= 0) ==>
      sum_repeated_elements_recursive(arr, start, length) >= 0;

    // Helper axiom: if all elements are positive, the sum is positive if there are repeated elements.
    // This helps the prover with ranges.
    axiom sum_repeated_elements_positive{L}(int[] arr, int start, int length) =
      (\forall integer i; start <= i < length ==> arr[i] > 0) &&
      (\exists integer i; start <= i < length && is_seen_before(arr, i, i)) ==>
      sum_repeated_elements_recursive(arr, start, length) > 0;
  }
*/

/*@
  requires N >= 0;
  // Prevent potential overflow of sum_repeated if elements are very large.
  // Assuming typical int range [-2^31, 2^31-1].
  // If all N elements are MAX_INT and repeated, sum could exceed int max.
  // This constraint limits N to prevent overflow of the result.
  // Max possible sum for N elements, if all are INT_MAX and repeated: N * INT_MAX.
  // To avoid overflow, N * INT_MAX <= INT_MAX, which implies N <= 1.
  // A more practical limit based on problem domain might be needed.
  // For this problem, assuming sum_repeated_elements_recursive will not overflow int.
  // If `arr` contains only positive values, `sum_repeated` will be positive.
  // If `arr` contains negative values, `sum_repeated` could be negative.
  // For safety, let's assume sum does not exceed typical int max/min.
  // The sum of 'N' elements, each up to INT_MAX, can overflow.
  // For example, if N=2 and both are INT_MAX, sum is 2*INT_MAX, which overflows.
  // A tighter bound on N or arr[i] is needed if INT_MAX is possible.
  // Let's constrain N to prevent overflow assuming elements are small enough,
  // or that INT_MAX / N is the max value for each element.
  // As a general rule, if sum can overflow, add a requires clause:
  // requires (\forall integer i; 0 <= i < N ==> arr[i] >= 0 && arr[i] <= INT_MAX / N);
  // However, the problem doesn't specify non-negative.
  // An alternative is to use long long for the sum, but problem asks for int.
  // Let's assume the sum will fit in an int for the given test cases.
  // Or, if any arr[i] is positive, the sum could overflow if N is large.
  // Let's add a general overflow prevention for the sum itself.
  requires N == 0 ||
           (\forall integer i; 0 <= i < N ==> arr[i] >= -20000 && arr[i] <= 20000); // Example: limit element values
  // This gives a max sum of 20000 * N. If N=10000, 200,000,000 fits in int.
  // If N=100000, 2,000,000,000 fits in int.
  // If N=1000000, 20,000,000,000 overflows int.
  // So, requires N <= 100000 (roughly) for this element range.
  // Let's use a more robust check:
  requires N == 0 || (\forall integer i; 0 <= i < N ==>
              (arr[i] >= 0 ? arr[i] <= INT_MAX / N : arr[i] >= INT_MIN / N));

  assigns \nothing;

  // Rule II.3: Use logical equivalence.
  ensures \result == sum_repeated_elements_recursive(arr, 0, N);
*/
int sum_of_repeated_elements(int arr[], int N) {
    int sum = 0;
    /*@
      loop invariant 0 <= i <= N;
      // 'sum' accumulates the sum of repeated elements found in arr[0..i-1].
      loop invariant sum == sum_repeated_elements_recursive(arr, 0, i);
      // 'seen' array tracks elements encountered so far in arr[0..i-1].
      // For this problem, a simple boolean array 'seen' isn't sufficient to find repeated
      // elements that have been seen *more than once*. It just tells if it's been seen at all.
      // To sum *repeated* elements, we need to know if an element is encountered again.
      // The current approach using `is_seen_before` in the axiomatic definition correctly
      // identifies elements that are repetitions. The loop needs to implement this.

      // Let's refine the loop invariant for 'sum'.
      // sum_repeated_elements_recursive(arr, 0, i) is the sum we expect.
      // Loop invariant for 'sum':
      // sum is the sum of arr[k] for 0 <= k < i, where arr[k] has appeared at least once
      // in arr[0..k-1].

      loop assigns sum, i;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        /*@
          loop invariant 0 <= j <= i;
          // Inner loop invariant:
          // 'found_duplicate' is 1 if arr[i] has been seen in arr[0..j-1].
          // This corresponds to is_seen_before(arr, i, i).
          loop invariant found_duplicate == (is_seen_before(arr, i, j) ? 1 : 0);
          loop assigns j, found_duplicate;
          loop variant i - j;
        */
        int found_duplicate = 0; // Rule I.2: int for boolean.
        for (int j = 0; j < i; j++) {
            if (arr[i] == arr[j]) {
                found_duplicate = 1;
                break;
            }
        }
        if (found_duplicate == 1) {
            // Rule II.5: Check for overflow before addition.
            // If sum + arr[i] could overflow, add a requires clause or check here.
            // Given the requires clause on element values and N, this should be safe.
            sum += arr[i];
        }
    }
    return sum;
}
