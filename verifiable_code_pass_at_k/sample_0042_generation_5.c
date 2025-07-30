// Task ID: 42
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in logic functions.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms are CRITICAL.
  // Rule II.3: ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Axiomatic block to define helper logic for array properties.
  axiomatic ArrayLogic {

    // Helper logic function to check if an element exists in a prefix of an array.
    // This is useful for checking if an element has been seen before.
    logic boolean exists_in_prefix{L}(int* a, int len, int val, int idx) =
      \exists integer k; 0 <= k < idx && k < len && a[k] == val;

    // Helper logic function to check if an element is repeated in an array up to a given index.
    // An element is 'repeated' if it appears at least twice in the array.
    // For the purpose of sum_of_repeated, we are interested if an element
    // appears at least once before the current index.
    logic boolean is_repeated_instance{L}(int* a, int len, int idx) =
      0 <= idx < len && exists_in_prefix(a, len, a[idx], idx);

    // Helper logic function to check if an element is the FIRST instance of a repeated element.
    // This helps avoid summing the same repeated element multiple times.
    logic boolean is_first_repeated_instance{L}(int* a, int len, int idx) =
      0 <= idx < len &&
      exists_in_prefix(a, len, a[idx], idx) && // It's repeated
      (\forall integer k; 0 <= k < idx ==> a[k] != a[idx]); // But it's the first time we see it *after* its first occurrence
      // This definition is slightly tricky. What we want is to sum the value
      // once if it appears multiple times. Let's redefine `is_repeated_value`
      // to mean that a value `v` exists at least twice in the array.
      // Then `is_first_occurrence_of_repeated_value` means `a[idx] == v`
      // and `idx` is the smallest index where `v` appears, and `v` is repeated.

    // A more robust way: define a value as "repeated" if it appears more than once.
    logic integer count_occurrences{L}(int* a, int len, int val) =
      \sum integer k; 0 <= k < len && a[k] == val;

    logic boolean is_value_repeated{L}(int* a, int len, int val) =
      count_occurrences(a, len, val) >= 2;

    // This logic function identifies if a[idx] is the *first* occurrence
    // of a value that is repeated elsewhere in the array.
    logic boolean is_first_occurrence_of_repeated_value{L}(int* a, int len, int idx) =
      0 <= idx < len &&
      is_value_repeated(a, len, a[idx]) &&
      (\forall integer k; 0 <= k < idx ==> a[k] != a[idx]);

  }
*/

/*@
  requires N >= 0;
  // Rule II.5: Prevent potential overflow if elements are large and sum can exceed INT_MAX.
  // Assuming array elements are positive for simplicity; if negative, sum can be negative.
  // For `int`, max sum is (N/2) * INT_MAX if all are INT_MAX and repeated.
  // Let's constrain elements to prevent overflow of the sum.
  // If `N` is large, elements must be small.
  // A simple constraint for safety: abs(a[i]) <= INT_MAX / N.
  // This is a strong constraint, but ensures no overflow.
  // For this problem, let's assume sum fits in int.
  // A more precise bound would be:
  // \sum integer i; 0 <= i < N && is_first_occurrence_of_repeated_value(a, N, i) ? (integer)a[i] : 0;
  // This sum must fit in an int.
  // Let's add a loose bound on elements to prevent obvious overflow.
  requires \forall integer k; 0 <= k < N ==> (integer)a[k] >= -2000000 && (integer)a[k] <= 2000000;
  // The sum of N/2 elements, each 2*10^6, could be N*10^6.
  // If N = 10000, sum could be 10^10, which overflows int.
  // So, let's assume N is small or elements are small.
  requires N <= 10000; // Max N for which sum of small elements fits in int.
  // The actual sum cannot exceed INT_MAX.
  // The sum of repeated elements cannot exceed N * max_element_value.
  // Requires: N * (max element value) <= INT_MAX
  // For INT_MAX approx 2*10^9, if N=10000, max element value is 2*10^5.
  requires \forall integer k; 0 <= k < N ==> (integer)a[k] >= -200000 && (integer)a[k] <= 200000;

  assigns \nothing;

  // Rule II.3: The ensures clause uses logical equivalence.
  // The result is the sum of unique values that appear at least twice in the array.
  ensures \result == (\sum integer i; 0 <= i < N && is_first_occurrence_of_repeated_value(a, N, i) ? (integer)a[i] : 0);
*/
int sum_of_repeated(int* a, int N) {
    int sum = 0;
    /*@
      loop invariant 0 <= i <= N;
      // The sum accumulated so far is the sum of first occurrences of repeated
      // values found in the prefix a[0..i-1].
      loop invariant sum == (\sum integer k; 0 <= k < i && is_first_occurrence_of_repeated_value(a, N, k) ? (integer)a[k] : 0);
      loop assigns i, sum;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        /*@
          // Inner loop invariant to check if a[i] has been seen before in the prefix a[0..i-1].
          loop invariant 0 <= j <= i;
          // count_current_val stores the number of times a[i] has appeared in a[0..j-1].
          loop invariant count_current_val == (\sum integer k; 0 <= k < j && a[k] == a[i] ? 1 : 0);
          loop assigns j, count_current_val;
          loop variant i - j;
        */
        int count_current_val = 0;
        for (int j = 0; j < i; j++) {
            if (a[j] == a[i]) {
                count_current_val++;
            }
        }

        // Now, count_current_val holds the number of times a[i] appeared before index i.
        // If count_current_val is 0, it means this is the first occurrence of a[i] in a[0..i].
        // We only add a[i] to the sum if:
        // 1. This is the first time we encounter a[i] (count_current_val == 0).
        // 2. a[i] is actually repeated *later* in the array.
        // To check condition 2, we need another loop, or rely on the `is_first_occurrence_of_repeated_value` logic.

        // The current loop structure sums `a[i]` if it's the first time it appears in the array
        // (i.e., `count_current_val == 0`) AND it appears *at least once more* in the rest of the array.
        // This is equivalent to `is_first_occurrence_of_repeated_value(a, N, i)`.

        if (count_current_val == 0) {
            /*@
              // Check if a[i] appears again in the rest of the array (from i+1 to N-1).
              loop invariant i < k <= N;
              loop invariant found_later == (\exists integer l; i < l < k && a[l] == a[i]);
              loop assigns k, found_later;
              loop variant N - k;
            */
            int found_later = 0;
            for (int k = i + 1; k < N; k++) {
                if (a[k] == a[i]) {
                    found_later = 1;
                    break;
                }
            }

            if (found_later) {
                // Rule II.5: Check for overflow before adding to sum.
                // Assuming sum + a[i] won't overflow based on requires clause.
                sum += a[i];
            }
        }
    }
    return sum;
}
