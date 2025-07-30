// Task ID: 34
// Generation: 3

/*@
  requires size >= 0;
  // All elements must be non-negative.
  requires \forall integer k; 0 <= k < size ==> a[k] >= 0;
  // The array must be sorted in ascending order.
  requires \forall integer k; 0 <= k < size - 1 ==> a[k] < a[k+1];
  // All elements must be distinct. (Implied by sorted + distinct values)
  // requires \forall integer k1, k2; 0 <= k1 < k2 < size ==> a[k1] != a[k2];
  
  // The elements are taken from the range [0, size].
  // This implies that a[k] <= size for all k.
  requires \forall integer k; 0 <= k < size ==> a[k] <= size;

  assigns \nothing;

  // Axiomatic definition to check if a specific number 'x' is present in the array.
  // This is crucial for verifying the postcondition.
  axiomatic MissingNumber {
    logic boolean is_present(int* arr, int sz, int x);

    axiom is_present_base:
      \forall int* arr, int sz, int x; sz <= 0 ==> !is_present(arr, sz, x);

    axiom is_present_recursive:
      \forall int* arr, int sz, int x; sz > 0 ==>
        (is_present(arr, sz, x) <==> (arr[sz-1] == x || is_present(arr, sz-1, x)));
  }

  // The function finds the unique integer 'm' such that 0 <= m <= size
  // and 'm' is not present in the array 'a', but all other integers
  // in the range [0, size] are present.

  // Helper axiom: If a number is present, it must be within the range [0, size].
  // This helps the prover relate the array contents to the expected range.
  axiom is_present_range_helper:
    \forall int* arr, int sz, int x;
      is_present(arr, sz, x) ==> 0 <= x && x <= sz;

  // Helper axiom: If array is sorted and distinct, then if x is present,
  // there is an index k such that arr[k] == x.
  // This is implicitly covered by the definition of is_present.

  // The ensures clause must capture the essence of "missing number".
  // It means the result 'res' is not in the array, AND all other numbers
  // in the range [0, size] ARE in the array.
  ensures 0 <= \result && \result <= size;
  ensures !is_present(a, size, \result);
  ensures \forall integer k; 0 <= k <= size && k != \result ==> is_present(a, size, k);
*/
int find_missing_number(int* a, int size) {
    /*@
      loop invariant 0 <= i && i <= size;
      // All numbers from 0 to i-1 are present in the array and match their indices.
      loop invariant \forall integer k; 0 <= k < i ==> a[k] == k;
      // For all numbers j from 0 to i-1, j is present in the array.
      loop invariant \forall integer j; 0 <= j < i ==> is_present(a, size, j);
      // The array remains sorted and within bounds for the remaining part.
      loop invariant \forall integer k; i <= k < size ==> a[k] <= size;
      loop invariant \forall integer k; i <= k < size - 1 ==> a[k] < a[k+1];
      loop assigns i;
      loop variant size - i;
    */
    for (int i = 0; i < size; ++i) {
        if (a[i] != i) {
            return i;
        }
    }
    // If the loop completes, it means a[i] == i for all i from 0 to size-1.
    // So, 0, 1, ..., size-1 are all present.
    // The missing number must be 'size'.
    return size;
}
