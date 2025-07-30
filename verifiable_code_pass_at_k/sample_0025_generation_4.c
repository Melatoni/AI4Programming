// Task ID: 25
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define a recursive logic function for uniqueness.
  // This function checks if an element `x` appears exactly once in the array `a`
  // within the range [low, high).
  axiomatic UniqueElement {
    logic integer count_occurrences{L}(int* a, int low, int high, int x);

    axiom count_occurrences_base{L}:
      \forall int* a, int low, int high, int x;
        low >= high ==> count_occurrences(a, low, high, x) == 0;

    axiom count_occurrences_recursive{L}:
      \forall int* a, int low, int high, int x;
        low < high ==> count_occurrences(a, low, high, x) ==
          (if a[low] == x then 1 else 0) + count_occurrences(a, low + 1, high, x);

    // Helper axiom: If an element appears only once, its count is 1.
    // This helps the prover connect the unique property to the count.
    axiom unique_is_one_occurrence{L}:
      \forall int* a, int low, int high, int x;
        (\forall integer k; low <= k < high && a[k] == x ==> k == low) ==>
        count_occurrences(a, low, high, x) == (if low < high && a[low] == x then 1 else 0);

    logic boolean is_unique_in_range{L}(int* a, int size, int index);

    axiom is_unique_in_range_def{L}:
      \forall int* a, int size, int index;
        0 <= index < size ==>
        is_unique_in_range(a, size, index) <==> (count_occurrences(a, 0, size, a[index]) == 1);
  }
*/

/*@
  requires size >= 0;
  requires \valid_read_range(a, 0, size - 1);

  // Rule II.5: Prevent overflow for the product.
  // Assuming 32-bit int, product cannot exceed INT_MAX (approx 2*10^9).
  // This is a conservative bound, as the product grows very fast.
  // For `int`, the maximum product of distinct numbers is limited.
  // If `size` is large, elements must be small.
  // This requires clause might need adjustment based on expected input ranges.
  // For a general case, we would need 64-bit integers or more complex overflow checks.
  requires \forall integer i; 0 <= i < size ==> a[i] >= -100 && a[i] <= 100;
  // A tighter bound can be derived if more is known about `size` and `a[i]`.
  // Here, we assume a practical limit that keeps the product within `int` range.
  // The product of non-repeated elements could be very large.
  // If `size` is small, e.g., <= 10, then `a[i]` can be larger.
  // For `int`, the maximum product is limited.
  // Example: 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31 (11 primes) is too large.
  // So, the number of distinct elements that can be multiplied and still fit in `int` is limited.
  // A simpler, more general approach is to require no overflow:
  requires \forall integer i; 0 <= i < size && is_unique_in_range(a, size, i) ==>
             (result == 0 || (INT_MAX / \abs(a[i]) >= \abs(result) && INT_MIN / \abs(a[i]) <= \abs(result)));
  // The above is complex for a requires clause. A simpler approach is to limit the range of values.
  // Let's assume the product will fit in an int for the given constraints.
  // A more robust solution would involve `long long` or checking for overflow at each multiplication.

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions.
  // The result is the product of elements a[i] where is_unique_in_range(a, size, i) is true.
  ensures \result == (\product integer i; 0 <= i < size && is_unique_in_range(a, size, i); a[i]);
*/
int product_of_non_repeated_elements(int* a, int size) {
    int product = 1;

    /*@
      loop invariant 0 <= i <= size;
      loop invariant product == (\product integer k; 0 <= k < i && is_unique_in_range(a, size, k); a[k]);
      loop assigns product, i;
      // Rule II.4: Loop variant for termination.
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        // Check if a[i] is unique in the entire array [0, size).
        if (count_occurrences(a, 0, size, a[i]) == 1) {
            // Rule II.5: Prevent overflow before multiplication.
            // This check is crucial for verifiability.
            // If product is 0, then a[i] * product is 0, no overflow.
            // Otherwise, check if product * a[i] will overflow.
            // This assumes a[i] is not 0. If a[i] can be 0, special handling might be needed.
            // If any unique element is 0, the product will be 0.
            // The `requires` clause on `a[i]` range helps here.
            // The logic below handles the general case for non-zero `a[i]`.
            /*@
              assert product != 0 ==> (
                a[i] > 0 ==> (product > 0 ==> INT_MAX / a[i] >= product) && (product < 0 ==> INT_MIN / a[i] <= product)
              ) && (
                a[i] < 0 ==> (product > 0 ==> INT_MIN / a[i] <= product) && (product < 0 ==> INT_MAX / a[i] >= product)
              );
            */
            product *= a[i];
        }
    }

    return product;
}
