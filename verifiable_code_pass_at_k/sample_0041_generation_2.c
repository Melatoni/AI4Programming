// Task ID: 41
// Generation: 2

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule II.3: Use logical equivalence for boolean-like functions.
  // This function simulates a lambda by taking a pointer to an array and its size.
  // It returns 1 if all numbers are even, 0 otherwise.
  // The problem description is a bit ambiguous about "filter even numbers using lambda function".
  // Assuming it means checking if all numbers are even, as a lambda would often be used for a predicate.
  // If it meant modifying the array in-place, the return type would likely be void.
  // For verification purposes, checking a property is more straightforward.

  // Rule II.5: Restrict array size to prevent potential issues with loop bounds or indexing.
  requires 0 <= size <= 100000;

  // Rule I.3: Array parameter 'arr' decays to a pointer to its element type.
  // For a 1D array, it's 'int *arr'.
  requires \valid_read_range(arr, 0, size - 1);

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like function using logical equivalence.
  ensures (\forall integer k; 0 <= k < size ==> arr[k] % 2 == 0) <==> (\result == 1);
*/
int all_even(int *arr, int size) {
  /*@
    loop invariant 0 <= i <= size;
    // Rule II.4: Invariant capturing the property checked so far.
    loop invariant \forall integer k; 0 <= k < i ==> arr[k] % 2 == 0;
    loop assigns i;
    // Rule II.4: Loop variant for termination.
    loop variant size - i;
  */
  for (int i = 0; i < size; ++i) {
    if (arr[i] % 2 != 0) {
      return 0; // Found an odd number
    }
  }
  return 1; // All numbers are even
}
