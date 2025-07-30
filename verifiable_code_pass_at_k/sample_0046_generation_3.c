// Task ID: 46
// Generation: 3

/*@
  // Rule I.2: Use int for boolean return type.
  // Rule II.5: Requires clause to prevent potential overflow if array elements are too large
  //            or if the array size is extremely large (though not directly used in this case).
  //            For `different` function, we mostly care about the range of elements themselves.
  //            Assuming elements are within `int` range, no specific overflow check needed for logic.
  // Rule I.3: Array parameters decay to pointers. `int *a` for `int a[]`.
  //           For `int a[N]`, it becomes `int *a`.
  //           For `int a[R][C]`, it becomes `int (*a)[C]`.
  //           Here, it's a 1D array.
  requires N >= 0;
  requires \valid_read_range(a, 0, N - 1);

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // \forall integer i, j; 0 <= i < j < N ==> a[i] != a[j]
  // This is the definition of all elements being different.
  ensures (\forall integer i, j; 0 <= i < j < N ==> a[i] != a[j]) <==> (result == 1);
*/
int are_all_different(int *a, int N) {
  /*@
    loop invariant 0 <= i <= N;
    // Invariant: All elements in a[0...i-1] are different from each other.
    loop invariant \forall integer k, l; 0 <= k < l < i ==> a[k] != a[l];
    // Invariant: All elements in a[0...i-1] are different from elements in a[i...N-1] checked so far.
    // This is implicitly handled by the inner loop's invariant and the outer loop's progress.
    // A simpler approach is to focus on the property that if we haven't returned yet,
    // all pairs (k,l) where k < i and l < i have been checked and are different.
    loop assigns i;
    // Rule II.4: A loop variant is mandatory for termination.
    loop variant N - i;
  */
  for (int i = 0; i < N; ++i) {
    /*@
      loop invariant i < j <= N;
      // Invariant: a[i] is different from all elements a[i+1...j-1].
      loop invariant \forall integer k; i < k < j ==> a[i] != a[k];
      loop assigns j;
      // Rule II.4: A loop variant is mandatory for termination.
      loop variant N - j;
    */
    for (int j = i + 1; j < N; ++j) {
      if (a[i] == a[j]) {
        return 0; // Found two identical elements, so they are not all different.
      }
    }
  }
  return 1; // All pairs checked, no identical elements found.
}
