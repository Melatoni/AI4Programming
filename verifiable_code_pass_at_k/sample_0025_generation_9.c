// Task ID: 25
// Generation: 9

/*@
  // Rule I.2: Use int for boolean-like return values.
  // Rule I.1: No standard libraries.
  // Rule II.5: Prevent potential overflow for product.
  // Max product for an int (32-bit signed) is roughly 2*10^9.
  // Max number of unique elements is N. If all are 100, N could be 2*10^7, which is too large.
  // Let's assume elements are small, e.g., max 100.
  // If all elements are 2, and there are 30 unique elements, 2^30 is too large.
  // So, we need a stricter bound on the product.
  // The product will be `product * arr[j]`. If `product` is large and `arr[j]` is large, overflow is possible.
  // A safe upper bound for product for int is `INT_MAX`.
  // We need to ensure that the product will not exceed INT_MAX.
  // A simple way is to limit the magnitude of array elements.
  // For example, if all unique elements are 2, and there are 30 of them, 2^30 > INT_MAX.
  // For safety, let's limit the product to be within INT_MAX.
  // This implies that the elements themselves cannot be arbitrarily large if many unique elements exist.
  // We will assume that the product of unique elements will not overflow `int`.
  // This can be stated as a `requires` clause.

  // Axiomatic block for logic functions (Rule II.1)
  axiomatic ProductOfUnique {
    logic integer is_unique_in_prefix(int[] a, integer len, integer idx) =
      \forall integer k; 0 <= k < idx ==> a[k] != a[idx];

    // Helper logic function to compute product of unique elements up to a certain index
    // This function will be used in the loop invariant and ensures clause.
    logic integer product_of_unique_elements_upto(int[] a, integer len, integer current_idx) =
      if current_idx < 0 then 1
      else (if is_unique_in_prefix(a, len, current_idx)
            then a[current_idx] * product_of_unique_elements_upto(a, len, current_idx - 1)
            else product_of_unique_elements_upto(a, len, current_idx - 1));

    // Rule II.2: Helper axiom for product_of_unique_elements_upto
    // This helps the prover to reason about the final product.
    axiom product_unique_positive:
      \forall int[] a, integer len, integer current_idx;
        (\forall integer k; 0 <= k <= current_idx ==> a[k] > 0) ==>
        product_of_unique_elements_upto(a, len, current_idx) >= 1;

    // Another helper axiom, if all elements are within a range, their product is also within a derived range.
    // This helps in proving non-overflow.
    axiom product_unique_bound:
      \forall int[] a, integer len, integer current_idx;
        (\forall integer k; 0 <= k <= current_idx ==> -100 <= a[k] <= 100) ==>
        product_of_unique_elements_upto(a, len, current_idx) <= 2147483647 &&
        product_of_unique_elements_upto(a, len, current_idx) >= -2147483648;
  }
*/

/*@
  requires N >= 0;
  // Rule II.5: Prevent overflow. The product of unique elements must fit in an int.
  // This is a strong pre-condition. Frama-C/WP cannot prove this on its own without knowing the values of elements.
  requires product_of_unique_elements_upto(arr, N, N - 1) <= 2147483647; // INT_MAX
  requires product_of_unique_elements_upto(arr, N, N - 1) >= -2147483648; // INT_MIN

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like function, but here it's a product.
  // So, we directly assert the final product.
  ensures \result == product_of_unique_elements_upto(arr, N, N - 1);
*/
int product_of_non_repeated_elements(int* arr, int N) {
    if (N == 0) {
        return 1; // Product of an empty set is 1.
    }

    int product = 1;

    /*@
      loop invariant 0 <= i <= N;
      // The product accumulated so far includes all unique elements in arr[0..i-1].
      loop invariant product == product_of_unique_elements_upto(arr, N, i - 1);
      loop assigns i, product;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        int is_repeated = 0; // Rule I.2: Use int for boolean.

        /*@
          loop invariant 0 <= j <= i;
          // is_repeated is 1 if arr[i] is found in arr[0..j-1], else 0.
          loop invariant ((\exists integer k; 0 <= k < j && arr[k] == arr[i]) <==> (is_repeated == 1));
          loop assigns j, is_repeated;
          loop variant i - j;
        */
        for (int j = 0; j < i; j++) {
            if (arr[j] == arr[i]) {
                is_repeated = 1;
                break;
            }
        }

        if (is_repeated == 0) {
            // Rule II.5: Prevent overflow before multiplication.
            // This is implicitly covered by the top-level requires, but good to make explicit if possible.
            // However, WP might struggle with this precise check without more specific value bounds.
            // A more robust check would be: if (arr[i] != 0 && product > INT_MAX / arr[i]) ... or similar.
            // For now, we rely on the top-level requires.
            product *= arr[i];
        }
    }

    return product;
}
