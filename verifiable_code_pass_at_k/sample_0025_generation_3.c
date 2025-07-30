// Task ID: 25
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define recursive logic for properties over arrays.
  // This axiomatic block defines a concept of an element being "unique"
  // within a given prefix of an array.
  axiomatic UniqueElement {
    logic boolean is_unique_in_prefix(int[] arr, int len, int val, int idx);

    // An element at idx is unique in the prefix arr[0..len-1]
    // if it's the first occurrence of its value up to idx,
    // and if its value is not present between idx+1 and len-1.
    // This is a more complex definition for product of *non-repeated* elements.
    // A non-repeated element is one that appears exactly once in the entire array.

    // Let's redefine 'non_repeated' to mean "appears exactly once in the whole array".
    logic integer count_occurrences(int[] arr, int len, int val, int current_idx);

    axiom count_occurrences_base:
      \forall int[] arr, int len, int val, int current_idx;
        current_idx >= len ==> count_occurrences(arr, len, val, current_idx) == 0;

    axiom count_occurrences_recursive:
      \forall int[] arr, int len, int val, int current_idx;
        current_idx < len ==>
          count_occurrences(arr, len, val, current_idx) ==
            (if arr[current_idx] == val then 1 else 0) + count_occurrences(arr, len, val, current_idx + 1);

    logic boolean is_non_repeated(int[] arr, int len, int val);
    axiom is_non_repeated_def:
      \forall int[] arr, int len, int val;
        is_non_repeated(arr, len, val) <==> (count_occurrences(arr, len, val, 0) == 1);

    // Logic to calculate the product of non-repeated elements
    logic integer product_non_repeated_elements(int[] arr, int len, int idx);

    axiom product_non_repeated_elements_base:
      \forall int[] arr, int len, int idx;
        idx >= len ==> product_non_repeated_elements(arr, len, idx) == 1;

    axiom product_non_repeated_elements_recursive:
      \forall int[] arr, int len, int idx;
        idx < len ==>
          product_non_repeated_elements(arr, len, idx) ==
            (if is_non_repeated(arr, len, arr[idx]) then arr[idx] else 1) * product_non_repeated_elements(arr, len, idx + 1);

    // Rule II.2 Helper Axiom: If all elements are within a range, their product is also.
    // This is a very basic helper, more specific ones might be needed for actual proof.
    // For example, if all non-repeated elements are positive, the product is positive.
    axiom product_positive_helper:
      \forall int[] arr, int len, int idx;
        (\forall integer k; idx <= k < len && is_non_repeated(arr, len, arr[k]) ==> arr[k] > 0) ==>
          product_non_repeated_elements(arr, len, idx) > 0;
  }
*/

/*@
  requires n >= 0;
  requires \valid_read_range(arr, 0, n - 1);

  // Rule II.5: Prevent overflow of the product.
  // This is a very strong requirement. For a given `int` type, the product
  // must not exceed INT_MAX or go below INT_MIN.
  // Here, we assume the product fits in 'int'. A more robust solution might
  // use 'long long' or check intermediate products.
  requires \abs(product_non_repeated_elements(arr, n, 0)) <= INT_MAX;
  // A tighter bound based on individual element values might be needed,
  // e.g., if max element is M, then max product is M^N in worst case.
  // For `int`, max value is 2^31 - 1. So, `n` and `arr` values must be constrained.
  // Example: if n=1 and arr[0]=INT_MAX, product is INT_MAX.
  // If n=2 and arr={2, INT_MAX/2}, product is INT_MAX.
  // If n=3 and arr={2,2,2}, product is 8.
  // To avoid `\abs(product_non_repeated_elements(arr, n, 0)) <= INT_MAX;` not being provable,
  // we might need to add constraints on individual elements in `arr`.
  // For simplicity, we assume the final product fits.

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions not applicable here as it returns a product.
  // The ensures clause directly specifies the result.
  ensures \result == product_non_repeated_elements(arr, n, 0);
*/
int find_product_of_non_repeated_elements(int arr[], int n) {
    if (n == 0) {
        return 1; // Product of an empty set is 1.
    }

    int product = 1;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant product == product_non_repeated_elements(arr, n, 0) / product_non_repeated_elements(arr, n, i);
      // More precisely: product == (\product integer k; 0 <= k < i && is_non_repeated(arr, n, arr[k]); arr[k]);
      // This is hard to express without sum/product notation in ACSL.
      // The `product_non_repeated_elements` logic function is key here.
      // The invariant states that `product` holds the product of non-repeated elements
      // found so far in the prefix `arr[0...i-1]`.
      // The `product_non_repeated_elements(arr, n, 0) / product_non_repeated_elements(arr, n, i)`
      // captures the product of elements from index 0 to i-1 that are non-repeated in the *entire* array.
      // This invariant is tricky because `is_non_repeated` depends on the whole array `n`.

      // Let's refine the invariant to be more direct about `product`'s value.
      loop invariant product == product_non_repeated_elements(arr, n, 0) / product_non_repeated_elements(arr, n, i);
      // This relies heavily on the `product_non_repeated_elements` logic function.
      // A more granular invariant:
      // loop invariant product == (\product integer k; 0 <= k < i && is_non_repeated(arr, n, arr[k]); arr[k]);
      // Frama-C doesn't have a direct `\product` operator, hence the recursive `logic` function.
      // So, the current invariant is the best way to link the C variable to the ACSL logic.

      loop assigns product, i;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        int current_val = arr[i];
        int count = 0;

        /*@
          loop invariant 0 <= j <= n;
          loop invariant count == count_occurrences(arr, n, current_val, 0) - count_occurrences(arr, n, current_val, j);
          // More directly: count == (\numof integer k; 0 <= k < j && arr[k] == current_val);
          loop assigns count, j;
          loop variant n - j;
        */
        for (int j = 0; j < n; j++) {
            if (arr[j] == current_val) {
                count++;
            }
        }

        if (count == 1) {
            // Rule II.5: Prevent overflow before multiplication.
            // Check if `product * current_val` will overflow.
            // Requires: `product != 0` and `current_val != 0` to simplify cases.
            // If `product == 0` or `current_val == 0`, the product will be 0.
            // If `current_val` is 1 or -1, no overflow.
            // Otherwise, check:
            // if current_val > 0: `product <= INT_MAX / current_val` AND `product >= INT_MIN / current_val`
            // if current_val < 0: `product >= INT_MAX / current_val` AND `product <= INT_MIN / current_val`
            // This is implicitly covered by the top-level `requires \abs(product_non_repeated_elements(arr, n, 0)) <= INT_MAX;`
            // but for WP, it often needs explicit checks at the point of multiplication.
            // For now, we rely on the pre-condition that the final product fits.
            // If `current_val` is 0, it won't cause overflow, but it must be handled correctly in the product.
            // If `current_val` is 0 and non-repeated, the product becomes 0.
            if (current_val != 0 && product != 0) { // Avoid division by zero for limits check, and handle 0 correctly
                 /*@
                   requires (current_val > 0 && product <= INT_MAX / current_val && product >= INT_MIN / current_val) ||
                            (current_val < 0 && product >= INT_MAX / current_val && product <= INT_MIN / current_val) ||
                            current_val == 1 || current_val == -1 || product == 1 || product == -1;
                 */
                product *= current_val;
            } else if (current_val == 0) {
                product = 0; // If 0 is a non-repeated element, the product becomes 0.
            }
            // If product is already 0, and current_val is not 0, it remains 0.
            // No action needed if product is 0.
        }
    }

    return product;
}
