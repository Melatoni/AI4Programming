// Task ID: 19
// Generation: 5

/*@
  // Rule I.2: Use int for boolean return type.
  // Rule II.3: Ensures clause uses logical equivalence.
  ensures (\exists integer i, j; 0 <= i < j < n && a[i] == a[j]) <==> (result == 1);
  // Rule II.5: Prevent runtime errors. n must be non-negative.
  requires n >= 0;
  // Rule I.3: Array parameter decay. 'a' is a pointer to the first element.
  // The \valid axiom needs to know the size of the array.
  requires \valid_read_range(a, 0, n - 1);
  assigns \nothing;
*/
int contains_duplicate(int* a, int n) {
  /*@
    loop invariant 0 <= i <= n;
    // Rule II.4: Invariant for the outer loop.
    // All elements processed so far (a[0] to a[i-1]) do not have duplicates
    // among themselves, or a duplicate has already been found.
    loop invariant (\forall integer k, l; 0 <= k < l < i ==> a[k] != a[l]) || result == 1;
    loop assigns i, result; // Although result is not directly assigned in the loop, it's modified by return.
    loop variant n - i;
  */
  for (int i = 0; i < n; i++) {
    /*@
      loop invariant i < j <= n;
      // Rule II.4: Invariant for the inner loop.
      // a[i] has not been found to be a duplicate of any a[k] where i < k < j.
      loop invariant (\forall integer k; i < k < j ==> a[i] != a[k]) || result == 1;
      loop assigns j, result; // Similar to outer loop, result is modified by return.
      loop variant n - j;
    */
    for (int j = i + 1; j < n; j++) {
      if (a[i] == a[j]) {
        return 1;
      }
    }
  }
  return 0;
}
