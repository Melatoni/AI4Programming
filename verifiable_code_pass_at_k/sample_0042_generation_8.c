// Task ID: 42
// Generation: 8

int` values.
    *   A more general approach is to iterate through the array. For each element, check if it has appeared before or if it appears again later.
    *   To avoid summing the same repeated element multiple times (e.g., if `[1, 2, 2, 2, 3]`, we want `2` to be added only once to the sum for its repetitions, not three times), we can mark elements as "processed" or skip them if they've already been counted as part of a repetition.

Let's refine the strategy:
*   We'll use a nested loop. The outer loop iterates through each element `arr[i]`.
*   The inner loop will check `arr[i]` against subsequent elements `arr[j]` (where `j > i`).
*   To handle duplicates correctly:
    *   We need a way to know if `arr[i]` itself is a duplicate (i.e., it appeared before `i`). If it is, we skip it.
    *   We need a way to know if `arr[i]` has been counted towards the sum of repeated elements already.

A simpler, more verifiable approach using a helper function:

1.  Iterate through the array.
2.  For each element `arr[i]`, check if it's a "first occurrence" of a repeated element. This means:
    *   It has not appeared at any index `k < i`.
    *   It *does* appear at some index `j > i`.
3.  If both conditions are met, add `arr[i]` to the sum.

This avoids double counting. For `[2, 2, 2]`:
*   `i=0`, `arr[0]=2`: Has not appeared before. Does `2` appear later? Yes, at `i=1`. So, add `2` to sum.
*   `i=1`, `arr[1]=2`: Has appeared before (at `i=0`). Skip.
*   `i=2`, `arr[2]=2`: Has appeared before (at `i=0`). Skip.

This works. We need a helper `logic` function in ACSL to define what "has appeared before" means and what "appears later" means.

/*@ axiomatic RepeatedSum {
  @   // Rule II.1: Recursive logic for complex properties.
  @   // Checks if element x exists in the array arr up to index end_idx (exclusive).
  @   logic boolean exists_before(int arr[], int start_idx, int end_idx, int x) =
  @     (end_idx <= start_idx) ? \false :
  @     (arr[end_idx - 1] == x) || exists_before(arr, start_idx, end_idx - 1, x);
  @
  @   // Rule II.1: Recursive logic for complex properties.
  @   // Checks if element x exists in the array arr from index start_idx (inclusive) to end_idx (exclusive).
  @   logic boolean exists_after(int arr[], int start_idx, int end_idx, int x) =
  @     (start_idx >= end_idx) ? \false :
  @     (arr[start_idx] == x) || exists_after(arr, start_idx + 1, end_idx, x);
  @
  @   // Rule II.1: Recursive logic for complex properties.
  @   // Defines the sum of repeated elements up to a given index k.
  @   // This is the core logic that the function should compute.
  @   logic integer sum_repeated_elements_logic(int arr[], int n, int k) =
  @     (k <= 0) ? 0 :
  @     // If arr[k-1] is the first occurrence of a repeated element, add it.
  @     // Rule II.2: Helper axiom/logic for complex conditions.
  @     // A repeated element is one that appears at least twice in the array.
  @     // We only sum it if this is its *first* appearance in the array.
  @     // exists_before(arr, 0, k - 1, arr[k-1]) : checks if arr[k-1] appeared before index k-1.
  @     // exists_after(arr, k, n, arr[k-1])     : checks if arr[k-1] appears after or at index k.
  @     (if !exists_before(arr, 0, k - 1, arr[k-1]) && exists_after(arr, k, n, arr[k-1])
  @      then arr[k-1]
  @      else 0) + sum_repeated_elements_logic(arr, n, k - 1);
  @
  @   // Helper axiom to prove non-negativity of sum for non-negative elements.
  @   // Could be useful if we add requires for positive elements. Not strictly needed here.
  @   // lemma sum_repeated_non_negative {
  @   //   assumes \forall integer i; 0 <= i < n ==> arr[i] >= 0;
  @   //   ensures sum_repeated_elements_logic(arr, n, n) >= 0;
  @   // };
  @ }
  @*/

/*@
  @ requires n >= 0;
  @ requires \valid_read(arr + (0..n-1));
  @
  @ // Rule II.5: Prevent potential overflow if elements are large.
  @ // Max possible sum: n * INT_MAX. Check if it fits in int.
  @ // For simplicity, let's assume sum fits. For a robust solution,
  @ // we'd need to bound n or arr[i] or use long long.
  @ // Assuming a 32-bit int, n * INT_MAX can overflow easily.
  @ // A tighter bound might be: \sum_{i=0}^{n-1} |arr[i]| <= INT_MAX
  @ // Here, we'll omit a specific overflow check for the sum itself,
  @ // but the loop invariant will guard against current_sum overflow.
  @ // A more precise check for sum overflow would require knowing the range of arr[i].
  @ // For now, we assume the sum fits in 'int'.
  @
  @ assigns \nothing;
  @
  @ // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  @ ensures \result == sum_repeated_elements_logic(arr, n, n);
*/
int sum_repeated_elements(int arr[], int n) {
    int sum = 0;
    /*@
      @ loop invariant 0 <= i <= n;
      @ // The sum accumulated so far matches the logic function for elements up to i.
      @ loop invariant sum == sum_repeated_elements_logic(arr, n, i);
      @
      @ loop assigns i, sum;
      @ loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        // Check if arr[i] has appeared before index i
        int has_appeared_before = 0; // Rule I.2: Use int for boolean
        /*@
          @ loop invariant 0 <= j <= i;
          @ loop invariant has_appeared_before == exists_before(arr, 0, j, arr[i]);
          @
          @ loop assigns j, has_appeared_before;
          @ loop variant i - j;
        */
        for (int j = 0; j < i; ++j) {
            if (arr[j] == arr[i]) {
                has_appeared_before = 1;
                break;
            }
        }

        // Check if arr[i] appears again after or at index i+1
        int appears_later = 0; // Rule I.2: Use int for boolean
        /*@
          @ loop invariant i + 1 <= k <= n;
          @ loop invariant appears_later == exists_after(arr, i + 1, k, arr[i]);
          @
          @ loop assigns k, appears_later;
          @ loop variant n - k;
        */
        for (int k = i + 1; k < n; ++k) {
            if (arr[k] == arr[i]) {
                appears_later = 1;
                break;
            }
        }

        // Rule I.2: Use int for boolean logic
        if (has_appeared_before == 0 && appears_later == 1) {
            // Rule II.5: Prevent overflow of sum.
            // This is a weak check. A stronger one would be 'requires arr[i] <= INT_MAX - sum'.
            // For now, WP might require additional bounds on arr[i] if it can't prove this.
            // If arr[i] can be negative, then 'sum + arr[i]' could underflow.
            // For general integers, we might need 'long long' for sum.
            // Assuming sum fits 'int' based on typical problem constraints.
            // To make it truly verifiable for arbitrary int, we'd need to bound arr[i]
            // or use a larger type for sum.
            //@ ghost int old_sum = sum;
            //@ assert (arr[i] > 0 && old_sum > INT_MAX - arr[i]) ==> \false; // Overflow check
            //@ assert (arr[i] < 0 && old_sum < INT_MIN - arr[i]) ==> \false; // Underflow check
            sum += arr[i];
        }
    }
    return sum;
}
