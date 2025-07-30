// Task ID: 46
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here.

  // Rule II.5: Prevent Runtime Errors.
  // The maximum size of the array is constrained here to prevent potential
  // issues with integer overflow if 'size' were extremely large,
  // although for typical array sizes, this might not be strictly necessary
  // for the loop invariant itself.
  requires size >= 0 && size <= 100000; // Arbitrary reasonable upper bound for array size

  // Ensures no side effects on memory outside of local variables.
  assigns \nothing;

  // Axiomatic block for recursive logic (Rule II.1) - not strictly needed for this problem,
  // but demonstrating the structure.
  // For `all_different`, a direct ACSL quantification is simpler and more efficient.
  // However, if we needed to prove properties about sub-arrays or
  // more complex set properties, a recursive logic function would be used.
  // For example, to check if a prefix of an array is all different:
  // axiomatic AllDifferentPrefix {
  //   logic boolean is_prefix_all_different{L}(int* arr, integer len);
  //
  //   axiom is_prefix_all_different_base{L}:
  //     \forall int* arr; is_prefix_all_different(arr, 0);
  //
  //   axiom is_prefix_all_different_recursive{L}:
  //     \forall int* arr, integer len;
  //       len > 0 ==> (is_prefix_all_different(arr, len) <==>
  //                    (is_prefix_all_different(arr, len - 1) &&
  //                     (\forall integer k; 0 <= k < len - 1 ==> arr[k] != arr[len - 1])));
  // }

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  // The function returns 1 if all elements are different, 0 otherwise.
  ensures (\forall integer i, j; 0 <= i < size && 0 <= j < size && i != j ==> arr[i] != arr[j]) <==> (\result == 1);
*/
int all_different(int* arr, int size) {
    /*@
      // Rule II.4: Loop invariants and variant for the outer loop.
      loop invariant 0 <= i <= size;
      // All elements processed so far (arr[0]...arr[i-1]) are unique among themselves.
      loop invariant \forall integer k1, k2; 0 <= k1 < i && 0 <= k2 < i && k1 != k2 ==> arr[k1] != arr[k2];
      loop assigns i, j; // 'j' is assigned in the inner loop, but its scope is tied to 'i'.
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        /*@
          // Rule II.4: Loop invariants and variant for the inner loop.
          loop invariant i < j <= size;
          // The element arr[i] is different from all preceding elements arr[0]...arr[i-1],
          // and also different from elements arr[i+1]...arr[j-1].
          loop invariant \forall integer k; 0 <= k < i ==> arr[k] != arr[i];
          loop invariant \forall integer k; i < k < j ==> arr[k] != arr[i];
          loop assigns j;
          loop variant size - j;
        */
        for (int j = i + 1; j < size; j++) {
            if (arr[i] == arr[j]) {
                return 0; // Found a duplicate, return false (0).
            }
        }
    }
    return 1; // No duplicates found, return true (1).
}
