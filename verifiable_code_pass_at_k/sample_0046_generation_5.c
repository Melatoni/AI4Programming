// Task ID: 46
// Generation: 5

/*@
  // Rule II.1: Define a recursive logic function to check if numbers in a range are distinct.
  // This avoids non-ACSL constructs like \forall i,j, ...
  axiomatic DistinctNumbers {
  logic boolean are_distinct_in_range{L}(int* arr, int start, int end, int N);

  // Base case: An empty range or a single element range is always distinct.
  axiom are_distinct_base:
  orall int* arr, int start, int end, int N;
  (start >= end) ==> are_distinct_in_range(arr, start, end, N);

  // Recursive step: Check if the first element is distinct from the rest,
  // and then recursively check the rest of the range.
  axiom are_distinct_rec:
  orall int* arr, int start, int end, int N;
  (start < end) ==> (
  are_distinct_in_range(arr, start, end, N) <==>
  (
  (orall integer k; start < k <= end ==> arr[start] != arr[k]) &&
  are_distinct_in_range(arr, start + 1, end, N)
  )
  );

  // Rule II.2: Helper axiom to prove distinctness for a full array
  // based on distinctness of a sub-range. This helps the prover.
  axiom are_distinct_full_array_helper:
  orall int* arr, int N;
  (N > 0 && are_distinct_in_range(arr, 0, N - 1, N)) ==>
  (orall integer i, j; 0 <= i < N && 0 <= j < N && i != j ==> arr[i] != arr[j]);

  }
*/

/*@
  requires N >= 0;
  // Rule I.3: arr decays to a pointer, so use int* for the parameter type.
  assigns 
othing;
  // Rule II.3: Use logical equivalence for boolean-like return values.
  ensures (N == 0 || are_distinct_in_range(arr, 0, N - 1, N)) <==> (esult == 1);
*/
int are_all_numbers_distinct(int* arr, int N) {
  // If N is 0 or 1, all numbers are trivially distinct.
  if (N <= 1) {
    return 1;
  }

  /*@
    loop invariant 0 <= i <= N;
    // Rule II.4: Loop invariant for the outer loop.
    // All elements from arr[0] to arr[i-1] are distinct from each other.
    loop invariant orall integer k, l; 0 <= k < i && 0 <= l < i && k != l ==> arr[k] != arr[l];
    loop assigns i, j;
    loop variant N - i;
  */
  for (int i = 0; i < N - 1; i++) {
    /*@
      loop invariant i < j <= N;
      // Rule II.4: Loop invariant for the inner loop.
      // arr[i] is distinct from all elements arr[i+1] to arr[j-1].
      loop invariant orall integer k; i < k < j ==> arr[i] != arr[k];
      loop assigns j;
      loop variant N - j;
    */
    for (int j = i + 1; j < N; j++) {
      if (arr[i] == arr[j]) {
        return 0; // Found a duplicate
      }
    }
  }

  return 1; // No duplicates found
}
