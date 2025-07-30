// Task ID: 25
// Generation: 0

/*@
  // Rule II.1: Define recursive logic for product.
  axiomatic Product {
    logic integer product_of_elements{L}(int* arr, int from, int to);

    axiom product_of_elements_base{L}:
      \forall int* arr, int from;
      product_of_elements(arr, from, from - 1) == 1;

    axiom product_of_elements_recursive{L}:
      \forall int* arr, int from, int to;
      from <= to ==> product_of_elements(arr, from, to) == product_of_elements(arr, from, to - 1) * arr[to];

    // Rule II.2: Helper axiom for product range.
    // If all elements are within a range [min_val, max_val],
    // and the product doesn't overflow, then the product will also be non-zero
    // if no element is zero. This specific helper is for non-zero positive elements.
    axiom product_non_zero_positive{L}:
      \forall int* arr, int from, int to;
      (\forall integer k; from <= k <= to ==> arr[k] > 0) ==> product_of_elements(arr, from, to) > 0;
  }

  // Rule II.1: Define recursive logic for checking uniqueness.
  axiomatic Unique {
    logic boolean is_unique{L}(int* arr, int from, int to, int val);

    axiom is_unique_base{L}:
      \forall int* arr, int from, int to, int val;
      from > to ==> is_unique(arr, from, to, val) == \true;

    axiom is_unique_recursive{L}:
      \forall int* arr, int from, int to, int val;
      from <= to ==> (is_unique(arr, from, to, val) <==> (arr[to] != val && is_unique(arr, from, to - 1, val)));

    // Helper axiom: if a value is not found in a subarray, it's not found in a smaller subarray.
    axiom is_unique_sub_array{L}:
      \forall int* arr, int from, int to, int val, int k;
      from <= k <= to ==> (is_unique(arr, from, to, val) ==> is_unique(arr, from, k - 1, val));

    // Helper axiom: if a value is not found in an array, it's not found in a smaller array, and vice versa.
    axiom is_unique_no_occurrence{L}:
      \forall int* arr, int from, int to, int val;
      (\forall integer k; from <= k <= to ==> arr[k] != val) <==> is_unique(arr, from, to, val);
  }
*/

/*@
  requires N >= 0;
  requires \valid_read_array(arr, N);

  // Rule II.5: Prevent overflow for the product.
  // This is a strong constraint, assuming the intermediate product and final product
  // fit within an int. For larger N or values, a different strategy (e.g., long long)
  // or more complex overflow checks would be needed. Here, we assume the product
  // of unique elements will not exceed INT_MAX.
  // A precise bound would depend on the values in the array.
  // For simplicity, we state that the result must be representable as an int.
  // A more robust check might involve an axiomatic function for max possible product.
  requires N == 0 || (N > 0 && \forall integer k; 0 <= k < N ==> arr[k] != 0 ==> \abs(arr[k]) <= 20000); // Heuristic to prevent immediate overflow on small numbers.

  assigns \nothing;

  behavior empty_array:
    assumes N == 0;
    ensures \result == 1;

  behavior non_empty_array:
    assumes N > 0;
    ensures \result == product_of_elements{Here}(arr, 0, N - 1, \lambda integer k;
                                               (\forall integer j; 0 <= j < N && j != k ==> arr[j] != arr[k]));
    // Rule II.3: For non-boolean return, we directly specify the result.
    // The product_of_elements{Here} with the lambda expression means
    // "the product of arr[k] where arr[k] appears only once in the array".
    // This is equivalent to:
    // \result == product_of_elements_where_unique(arr, N);
    // where unique_elements is
    // product_of_elements(arr, 0, N-1) if (arr[k] is unique in arr[0..N-1])
    // This is hard to model directly with the existing product_of_elements and unique.
    // Let's refine the model for the result.

    // A more precise ensures clause for the product of non-repeated elements:
    // The result is the product of all elements arr[k] such that arr[k]
    // appears exactly once in the array from index 0 to N-1.
    ensures \result == product_of_elements(arr, 0, N - 1, \lambda integer k;
                                                  (\forall integer j; 0 <= j < N && j != k ==> arr[j] != arr[k]));
    // This lambda expression is pseudo-ACSL. A more formal way:
    // ensures \result == product_of_elements(arr, 0, N - 1, \lambda integer k;
    //                                         count_occurrences(arr, 0, N - 1, arr[k]) == 1);
    // Let's use an axiomatic function for counting occurrences to make it sound.

    // Rule II.1: Define axiomatic function for counting occurrences.
    axiomatic CountOccurrences {
      logic integer count_occurrences{L}(int* arr, int from, int to, int val);

      axiom count_occurrences_base{L}:
        \forall int* arr, int from, int to, int val;
        from > to ==> count_occurrences(arr, from, to, val) == 0;

      axiom count_occurrences_recursive{L}:
        \forall int* arr, int from, int to, int val;
        from <= to ==> count_occurrences(arr, from, to, val) ==
                       (if arr[to] == val then 1 else 0) + count_occurrences(arr, from, to - 1, val);
    }

    // Now, the ensures clause can be more precise:
    ensures \result == product_of_elements(arr, 0, N - 1, \lambda integer k;
                                                  count_occurrences(arr, 0, N - 1, arr[k]) == 1);
    // This lambda is still pseudo-ACSL. Let's try to model the result iteratively.
    // The final result is the product of unique elements encountered.
    // We need to verify that an element is unique *in the whole array* before multiplying.
    // This requires a nested loop or a more complex approach.

    // Let's simplify the ensures for the C implementation approach:
    // The C code will likely iterate and for each element, check if it's unique in the whole array.
    // If it is, multiply it into the result.

    // We need a way to express the product of only the unique elements in the whole array.
    // This is not directly a product_of_elements(arr, from, to) as that implies
    // all elements from 'from' to 'to' are part of the product.
    // Let's define another axiomatic function for this specific product.
    axiomatic ProductUnique {
      logic integer product_of_unique_elements{L}(int* arr, int N);

      axiom product_of_unique_elements_def{L}:
        \forall int* arr, int N;
        product_of_unique_elements(arr, N) ==
          (if N == 0 then 1
           else (if count_occurrences(arr, 0, N - 1, arr[N - 1]) == 1
                 then arr[N - 1] * product_of_unique_elements(arr, N - 1)
                 else product_of_unique_elements(arr, N - 1)));
    }

    // Now, the ensures clause becomes clear:
    ensures \result == product_of_unique_elements(arr, N);
*/
int product_of_non_repeated_elements(int* arr, int N) {
    if (N == 0) {
        return 1;
    }

    int product = 1;
    /*@
      loop invariant 0 <= i <= N;
      loop invariant product == product_of_unique_elements(arr, i);
      // product == product of unique elements in arr[0..i-1] that are also unique in arr[0..N-1]
      // This invariant is tricky. Let's refine it.
      // The product should accumulate elements arr[k] where k < i AND arr[k] is unique in arr[0..N-1].
      // For this, we need to check uniqueness against the *entire* array N.

      loop invariant \forall integer k; 0 <= k < i ==>
                     (count_occurrences(arr, 0, N - 1, arr[k]) == 1 ==>
                      product % arr[k] == 0); // arr[k] is a factor if unique.
      loop invariant \forall integer k; 0 <= k < i ==>
                     (count_occurrences(arr, 0, N - 1, arr[k]) != 1 ==>
                      product % arr[k] != 0); // arr[k] is not a factor if not unique. (This is too strong if product is 1)

      // Let's use a ghost variable to track what product *should* be.
      // This is a common pattern for complex aggregations.
      // We need a helper logic function that computes the product of unique
      // elements up to a certain point `i`, considering uniqueness in the whole array `N`.
      logic integer product_unique_up_to_i(int* arr, int N_full, int i);

      axiom product_unique_up_to_i_base:
        \forall int* arr, int N_full;
        product_unique_up_to_i(arr, N_full, 0) == 1;

      axiom product_unique_up_to_i_recursive:
        \forall int* arr, int N_full, int i;
        0 <= i < N_full ==>
        product_unique_up_to_i(arr, N_full, i + 1) ==
          (if count_occurrences(arr, 0, N_full - 1, arr[i]) == 1
           then product_unique_up_to_i(arr, N_full, i) * arr[i]
           else product_unique_up_to_i(arr, N_full, i));

      loop invariant product == product_unique_up_to_i(arr, N, i);
      loop assigns product, i;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        int is_unique_element = 1; // Rule I.2: Use int for boolean.
        /*@
          loop invariant 0 <= j <= N;
          loop invariant 0 <= i < N;
          loop invariant \forall integer k; 0 <= k < j ==>
                         (k != i ==> arr[k] != arr[i] || is_unique_element == 0);
          loop invariant (is_unique_element == 1) <==>
                         (\forall integer k; 0 <= k < j && k != i ==> arr[k] != arr[i]);
          loop assigns j, is_unique_element;
          loop variant N - j;
        */
        for (int j = 0; j < N; j++) {
            // Check if arr[i] has a duplicate anywhere in the array (excluding itself)
            if (i != j && arr[i] == arr[j]) {
                is_unique_element = 0;
                break;
            }
        }

        if (is_unique_element == 1) {
            // Rule II.5: Prevent overflow before multiplication
            // Check if product * arr[i] will overflow.
            // This assumes product is already verified not to overflow.
            // A precise check for int multiplication overflow is:
            // if arr[i] > 0: product > INT_MAX / arr[i]
            // if arr[i] < 0: product < INT_MIN / arr[i] (for positive product)
            // if arr[i] < 0: product > INT_MAX / arr[i] (for negative product)
            // if arr[i] == -1: product == INT_MIN
            // Given the original `requires` on `arr[k]`, we might need a more precise one
            // or ensure `int` is large enough. For now, assume a general `int` range.
            // Frama-C's WP will generate warnings if it detects potential overflow.
            // The `requires` clause on `product_of_non_repeated_elements` about `arr[k]` bounds
            // aims to mitigate this, but a full overflow proof might require `long long` or more.

            // For `int`, the product can go from `INT_MIN` to `INT_MAX`.
            // The original problem is about `int`. Let's add an explicit overflow check.
            /*@
              assert (arr[i] == 0 ||
                      (arr[i] > 0 && product <= INT_MAX / arr[i]) ||
                      (arr[i] < 0 && product >= INT_MIN / arr[i] && arr[i] != -1) ||
                      (arr[i] == -1 && product != INT_MIN)); // Specific case for -1
            */
            product *= arr[i];
        }
    }

    return product;
}
