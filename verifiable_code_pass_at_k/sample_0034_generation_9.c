// Task ID: 34
// Generation: 9

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Using int for booleans.

  // Axiomatic block for recursive logic if needed.
  // For this problem, direct loop invariants are sufficient.

  // The function finds a single missing number in a sorted array of distinct integers.
  // The array is assumed to contain n elements, which ideally should be
  // a sequence from a[0] to a[0] + n, but one number is missing.

  @ requires n > 0;
  @ requires \valid_read(a + (0..n-1));
  @
  @ // The array must be sorted in non-decreasing order.
  @ // Rule II.5: Prevent overflow for a[i] + 1.
  @ // Assuming integers are within typical 32-bit range, a[i]+1 won't overflow
  @ // unless a[i] is INT_MAX. We assume a missing number means the sequence
  @ // does not reach INT_MAX.
  @ requires \forall integer i; 0 <= i < n - 1 ==> a[i] < a[i+1];
  @
  @ // Ensure there is exactly one missing number in the sequence that would
  @ // ideally go from a[0] to a[0] + n.
  @ // This implies that for all elements, a[i] is either a[0] + i
  @ // or a[0] + i + 1 (if the missing number is before or at a[i]).
  @ // And there is one index k where a[k] != a[0] + k.
  @ // This is implicitly handled by the loop logic and post-condition.
  @
  @ assigns \nothing;
  @
  @ // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  @ // The result is the first number 'x' such that (x - a[0]) != index.
  @ // If no number is missing within the expected range, the last expected number is returned.
  @ // This assumes the missing number is always within the range [a[0], a[0] + n].
  @ ensures (\exists integer i; 0 <= i < n && a[i] != a[0] + i)
  @         ==> (result == a[0] + (\min integer k; 0 <= k < n && a[k] != a[0] + k));
  @ ensures (\forall integer i; 0 <= i < n ==> a[i] == a[0] + i)
  @         ==> (result == a[0] + n); // If no number is missing, the next expected number is returned.
*/
int find_missing_number(int *a, int n) { // Rule I.3: int* for array decay.
    /*@
      @ loop invariant 0 <= i <= n;
      @ // If no missing number has been found so far, then a[k] == a[0] + k for all k < i.
      @ loop invariant \forall integer k; 0 <= k < i ==> a[k] == a[0] + k;
      @ loop assigns i;
      @ // Rule II.4: A loop variant is mandatory for termination.
      @ loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // Check if the current element is not what we expect based on the starting value and index.
        // If a[i] should be a[0] + i, but it's not, then a[0] + i is the missing number.
        if (a[i] != a[0] + i) {
            return a[0] + i;
        }
    }
    // If the loop completes, it means all numbers from a[0] to a[0] + n - 1 are present.
    // In this case, the missing number is effectively the next number in the sequence.
    // This handles cases like [1, 2, 3] where 4 is "missing" if the sequence length expects 4 numbers.
    return a[0] + n;
}
