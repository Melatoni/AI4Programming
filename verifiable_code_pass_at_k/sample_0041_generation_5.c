// Task ID: 41
// Generation: 5

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule II.3: Use logical equivalence for boolean-like functions.
  // The function returns 1 if the number is even, 0 otherwise.
  ensures (n % 2 == 0) <==> (result == 1);
  assigns \nothing;
*/
int is_even(int n) {
  if (n % 2 == 0) {
    return 1; // True, n is even
  } else {
    return 0; // False, n is odd
  }
}

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for boolean-like values.
  // Rule I.3: Array pointer decay - arr is int*.
  // Rule II.5: Prevent runtime errors.
  //   - n must be non-negative for array indexing.
  //   - n must not exceed the maximum allowed size to prevent potential issues.
  requires n >= 0;
  requires n <= 10000; // Example constraint to prevent excessively large arrays or loops.

  // The output array `out` must be large enough to hold all elements.
  // In the worst case, all elements are even, so `out` needs to be of size `n`.
  // This is a common pattern for functions that modify an output array.
  // The caller is responsible for allocating `out` with sufficient capacity.
  // For simplicity, we assume `out` has at least `n` capacity.
  // A more robust solution might return the count and require `out` to be sized by the caller.

  // `assigns` clause:
  //   - `out[0..n-1]` indicates that elements of `out` up to `n-1` might be written to.
  //   - `\result` is assigned the count of even numbers.
  assigns out[0..n-1], \result;

  // Rule II.3: Ensures clause for the return value (count of even numbers).
  // The result should be equal to the number of elements in `arr` that are even.
  ensures \result == (\num_of(integer k; 0 <= k < n && is_even(arr[k]) == 1));

  // The elements in `out` up to `\result - 1` must be the even numbers from `arr`,
  // in their original relative order.
  ensures \forall integer i; 0 <= i < \result ==>
            (\exists integer j; 0 <= j < n && arr[j] == out[i] && is_even(arr[j]) == 1 &&
              // Maintain relative order:
              (\forall integer k; 0 <= k < i ==>
                 (\exists integer l; 0 <= l < j && arr[l] == out[k] && is_even(arr[l]) == 1)));

  // All elements in `out` from `\result` to `n-1` are unspecified/unmodified beyond the result.
  // This is typically not explicitly stated in `ensures` but implied by `assigns` and the first `ensures`.
  // More precisely, elements beyond `\result - 1` are not guaranteed to be even numbers from `arr`.
*/
int filter_even(int arr[], int n, int out[]) {
  int count = 0;
  /*@
    loop invariant 0 <= i <= n;
    loop invariant 0 <= count <= i;

    // Rule II.4: Loop invariant for `out` array content and its relationship with `arr`.
    // All elements in `out` up to `count-1` are even numbers from `arr`, in order.
    loop invariant \forall integer k; 0 <= k < count ==>
                      (\exists integer j; 0 <= j < i && arr[j] == out[k] && is_even(arr[j]) == 1 &&
                        (\forall integer l; 0 <= l < k ==>
                           (\exists integer m; 0 <= m < j && arr[m] == out[l] && is_even(arr[m]) == 1)));

    // No even numbers from `arr[0..i-1]` have been missed.
    loop invariant \forall integer k; 0 <= k < i && is_even(arr[k]) == 1 ==>
                      (\exists integer j; 0 <= j < count && out[j] == arr[k]);

    // The count of even numbers found so far matches the actual count in arr[0..i-1].
    loop invariant count == (\num_of(integer k; 0 <= k < i && is_even(arr[k]) == 1));

    loop assigns i, count, out[0..i-1]; // `out` elements up to `i-1` potentially assigned.
    loop variant n - i;
  */
  for (int i = 0; i < n; i++) {
    if (is_even(arr[i]) == 1) { // Rule I.2: Use 1 for true.
      out[count] = arr[i];
      count++;
    }
  }
  return count;
}
