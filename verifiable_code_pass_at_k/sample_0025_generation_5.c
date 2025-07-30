// Task ID: 25
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.

  // Axiomatic block for recursive logic.
  axiomatic NonRepeatedProduct {
    logic integer product_of_non_repeated_elements_in_range(int* arr, int start, int end, int N);

    axiom product_of_non_repeated_elements_in_range_base:
      for_all int* arr, int start, int N;
      product_of_non_repeated_elements_in_range(arr, start, start, N) == 1;

    axiom product_of_non_repeated_elements_in_range_recursive:
      for_all int* arr, int start, int end, int N;
      (start < end) ==>
      product_of_non_repeated_elements_in_range(arr, start, end, N) ==
      (if (\exists integer k; start <= k < end && arr[k] == arr[end])
       then product_of_non_repeated_elements_in_range(arr, start, end - 1, N)
       else (if (\exists integer k; end < k < N && arr[k] == arr[end])
             then product_of_non_repeated_elements_in_range(arr, start, end - 1, N)
             else arr[end] * product_of_non_repeated_elements_in_range(arr, start, end - 1, N)));

    // Helper axiom: if an element is found in the preceding part or succeeding part, it's considered repeated.
    logic boolean is_repeated_in_full_array(int* arr, int N, int index);
    axiom is_repeated_in_full_array_def:
      for_all int* arr, int N, int index;
      is_repeated_in_full_array(arr, N, index) <==>
      (\exists integer k; (0 <= k < index || index < k < N) && arr[k] == arr[index]);

    // Helper axiom for the main product logic
    logic integer non_repeated_product_recursive(int* arr, int N, int current_idx);

    axiom non_repeated_product_recursive_base:
      for_all int* arr, int N;
      non_repeated_product_recursive(arr, N, -1) == 1; // Base case for empty prefix

    axiom non_repeated_product_recursive_step:
      for_all int* arr, int N, int current_idx;
      (0 <= current_idx < N) ==>
      non_repeated_product_recursive(arr, N, current_idx) ==
      (if is_repeated_in_full_array(arr, N, current_idx)
       then non_repeated_product_recursive(arr, N, current_idx - 1)
       else arr[current_idx] * non_repeated_product_recursive(arr, N, current_idx - 1));

    // Helper axiom: product of an empty range is 1
    axiom product_empty_range:
      for_all int* arr, int start, int end, int N;
      (start >= end) ==> product_of_non_repeated_elements_in_range(arr, start, end, N) == 1;

    // Helper axiom: if all elements are positive, the product is positive.
    // This helps with proving non-overflow when elements are within range.
    axiom positive_elements_positive_product:
      for_all int* arr, int start, int end, int N;
      (\forall integer i; start <= i < end ==> arr[i] > 0) ==>
      product_of_non_repeated_elements_in_range(arr, start, end, N) > 0;

    // Helper axiom: if all elements are negative, the product sign depends on count.
    // This is more complex, but a general overflow prevention is usually sufficient.
  }
*/

/*@
  requires N >= 0;
  requires \valid_read(arr + (0..N-1));
  // Rule II.5: Prevent product overflow. Max product could be INT_MAX.
  // This is a very strong requirement. For a more general solution,
  // one might need to return a long long or handle overflow explicitly.
  // For 'int', the product must fit within 'int' range.
  // Assuming elements are within a reasonable range to avoid immediate overflow
  // for small N, e.g., if N=1, arr[0] must not overflow 'int'.
  // If N > 0, the product of non-repeated elements must fit in an int.
  requires N == 0 || non_repeated_product_recursive(arr, N, N-1) >= INT_MIN && non_repeated_product_recursive(arr, N, N-1) <= INT_MAX;

  assigns \nothing;

  ensures \result == non_repeated_product_recursive(arr, N, N-1);
*/
int product_of_non_repeated_elements(int* arr, int N) {
  if (N == 0) {
    return 1;
  }

  int product = 1;
  /*@
    loop invariant 0 <= i <= N;
    loop invariant product == non_repeated_product_recursive(arr, i, i-1);
    loop assigns product, i;
    loop variant N - i;
  */
  for (int i = 0; i < N; ++i) {
    int is_repeated = 0; // Rule I.2: Use int for boolean.
    /*@
      loop invariant 0 <= j <= i;
      loop invariant is_repeated == (\exists integer k; 0 <= k < j && arr[k] == arr[i]);
      loop assigns is_repeated, j;
      loop variant i - j;
    */
    for (int j = 0; j < i; ++j) {
      if (arr[j] == arr[i]) {
        is_repeated = 1;
        break;
      }
    }

    /*@
      loop invariant i < N;
      loop invariant is_repeated == (\exists integer k; (0 <= k < i || i < k_prime < j) && arr[k_prime] == arr[i]); // k_prime is used to avoid conflict with j
      loop assigns is_repeated, j;
      loop variant N - j;
    */
    for (int j = i + 1; j < N; ++j) {
      if (arr[j] == arr[i]) {
        is_repeated = 1;
        break;
      }
    }

    if (is_repeated == 0) { // Rule I.2: Use int for boolean.
      // Rule II.5: Prevent overflow before multiplication.
      // This is implicit in the function pre-condition, but a runtime check
      // or more granular proof would be needed for a less restrictive pre-condition.
      product *= arr[i];
    }
  }

  return product;
}
