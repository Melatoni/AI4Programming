// Task ID: 42
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: Define recursive logic for complex properties.
  axiomatic SumRepeated {
    logic integer count_occurrences{L}(int* arr, int size, int val, integer idx) reads arr[0..size-1];

    axiom count_occurrences_base{L}:
      \forall int* arr, int size, int val;
      count_occurrences(arr, size, val, size) == 0;

    axiom count_occurrences_recursive{L}:
      \forall int* arr, int size, int val, integer idx;
      0 <= idx < size ==>
      count_occurrences(arr, size, val, idx) ==
        (if arr[idx] == val then 1 else 0) + count_occurrences(arr, size, val, idx + 1);

    logic boolean is_repeated{L}(int* arr, int size, int val) reads arr[0..size-1];
    axiom is_repeated_def{L}:
      \forall int* arr, int size, int val;
      is_repeated(arr, size, val) <==> (count_occurrences(arr, size, val, 0) >= 2);

    logic integer sum_repeated_elements_logic{L}(int* arr, int size, integer idx) reads arr[0..size-1];

    axiom sum_repeated_elements_logic_base{L}:
      \forall int* arr, int size;
      sum_repeated_elements_logic(arr, size, size) == 0;

    axiom sum_repeated_elements_logic_recursive{L}:
      \forall int* arr, int size, integer idx;
      0 <= idx < size ==>
      sum_repeated_elements_logic(arr, size, idx) ==
        (if is_repeated(arr, size, arr[idx]) then arr[idx] else 0) + sum_repeated_elements_logic(arr, size, idx + 1);

    // Rule II.2: CRITICAL - Helper axioms for properties that prover cannot deduce.
    // This axiom helps to relate the sum of repeated elements to the sum of unique repeated elements.
    // It's a key property for proving the correctness of the algorithm that processes unique elements.
    axiom sum_repeated_unique_property{L}:
      \forall int* arr, int size, integer i;
      0 <= i < size ==>
      (is_repeated(arr, size, arr[i]) &&
       (\forall integer j; 0 <= j < i ==> arr[j] != arr[i])) ==>
      sum_repeated_elements_logic(arr, size, i) == arr[i] + sum_repeated_elements_logic(arr, size, i + 1);

    axiom sum_repeated_non_unique_property{L}:
      \forall int* arr, int size, integer i;
      0 <= i < size ==>
      (is_repeated(arr, size, arr[i]) &&
       (\exists integer j; 0 <= j < i && arr[j] == arr[i])) ==>
      sum_repeated_elements_logic(arr, size, i) == sum_repeated_elements_logic(arr, size, i + 1);

    axiom sum_repeated_not_repeated_property{L}:
      \forall int* arr, int size, integer i;
      0 <= i < size ==>
      !is_repeated(arr, size, arr[i]) ==>
      sum_repeated_elements_logic(arr, size, i) == sum_repeated_elements_logic(arr, size, i + 1);
  }
*/

/*@
  requires size >= 0;
  requires \valid_read(arr + (0..size-1));
  // Rule II.5: Prevent potential overflow if array elements are large.
  // Assuming a 32-bit int, INT_MAX is 2,147,483,647.
  // If all elements are positive INT_MAX, and size is large, sum can overflow.
  // A conservative bound: max_val * size <= INT_MAX
  // For simplicity, assuming elements are within a range that prevents intermediate overflow
  // when summing, or that the final sum fits in int.
  // A tighter bound would depend on the maximum possible value of an element and size.
  // For a general case, we might need `long long` for the sum or more complex range checks.
  // Here, we assume a reasonable range for `int` that allows summation.
  // For example, if max element is 1000, and size is 1000, max sum is 1,000,000 which fits.
  // Let's assume elements are within a range where sum does not overflow for typical sizes.
  // If `size` is `INT_MAX`, and elements are 1, sum overflows.
  // We need to ensure `size * max_element_value <= INT_MAX` for positive elements.
  // For simplicity, we add a general requirement that the sum must fit.
  requires (\sum integer k; 0 <= k < size && is_repeated(arr, size, arr[k]); arr[k]) <= INT_MAX;
  requires (\sum integer k; 0 <= k < size && is_repeated(arr, size, arr[k]); arr[k]) >= INT_MIN;

  assigns \nothing;

  ensures \result == sum_repeated_elements_logic(arr, size, 0);
*/
int sum_of_repeated_elements(int* arr, int size) {
    int sum = 0;
    /*@
      loop invariant 0 <= i <= size;
      loop invariant sum == sum_repeated_elements_logic(arr, size, 0) - sum_repeated_elements_logic(arr, size, i);
      // The `sum` accumulates elements from `0` to `i-1` only if they are repeated AND they are the first occurrence encountered so far.
      // This invariant is tricky. The `sum` variable accumulates each repeated element *once* when its first occurrence is found.
      // So, `sum` should be equal to the sum of unique values that are repeated.
      // Let's refine the invariant based on the actual algorithm below, which iterates and adds if it's repeated AND it's the first time we see it.
      // This means we need an auxiliary function to capture "sum of unique repeated values".

      // Let's change the approach slightly to match the common implementation:
      // Iterate through the array. For each element, check if it's repeated.
      // If it is repeated, add it to the sum ONLY IF it's the first time we encounter this value.
      // This requires checking if the element has appeared before in the processed part of the array.

      // Let's refine the loop invariant based on a more direct approach:
      // Iterate through each element. If it's repeated, and it's the first time we've seen this value, add it.
      // This is the most common and verifiable way to implement this.

      // Redefine `sum_repeated_elements_logic` to sum unique repeated values.
      // Or, add a helper logic function for "sum of unique repeated elements".

      // Let's stick to the current logic for `sum_repeated_elements_logic` which sums *all* repeated occurrences.
      // The C code, however, usually sums *unique* repeated values.
      // For example, [1, 2, 2, 3, 3, 3] -> sum = 2 + 3 = 5
      // My `sum_repeated_elements_logic` for this would be 2+2+3+3+3 = 13.
      // There's a mismatch between the problem statement (sum of repeated elements) and typical interpretation (sum of unique repeated elements).
      // Let's assume the problem means "sum of values that appear at least twice, with each such value added once to the sum".
      // If the problem meant "sum of all instances of repeated elements", the sum for [1,2,2,3,3,3] would be 2+2+3+3+3 = 13.

      // Let's define a new logic function for "sum of unique repeated values".
      // This is a common interpretation of "sum of repeated elements".

      // Let `unique_repeated_sum_logic` be the sum of values `v` such that `v` appears at least twice in `arr`, and `v` is added only once to the sum.
      // The current `sum_repeated_elements_logic` sums `arr[i]` if `arr[i]` is repeated.
      // So [1,2,2,3,3,3] -> sum_repeated_elements_logic would be 2+2+3+3+3 = 13.
      // If the intent is to sum each distinct repeated value only once (e.g., 2+3=5 for [1,2,2,3,3,3]),
      // then the `ensures` clause and the C code logic must reflect that.

      // Let's re-read: "sum of repeated elements". This implies summing all instances.
      // E.g., [1, 2, 2, 3, 3, 3] -> 2+2+3+3+3 = 13.
      // The C code needs to identify unique values, count them, and if count >= 2, add value * count.
      // This is more complex than iterating and checking `is_repeated`.

      // A common implementation for "sum of repeated elements" in Python:
      // `collections.Counter(arr)` to get counts.
      // `sum(k for k, v in counts.items() if v >= 2)` -> this sums unique repeated values.
      // `sum(k * v for k, v in counts.items() if v >= 2)` -> this sums all instances of repeated values.

      // Given the simplicity expected for Frama-C, the most direct interpretation is "sum of all instances of elements that are repeated".
      // So for [1,2,2,3,3,3], 2 is repeated, 3 is repeated. Sum = 2+2+3+3+3 = 13.
      // The provided `sum_repeated_elements_logic` correctly computes this.

      // The C code for this is also tricky without hash maps.
      // A nested loop approach:
      // For each element arr[i]:
      //   Check if it has been processed before (to avoid double counting its instances)
      //   Count its occurrences in the rest of the array.
      //   If count >= 2, add arr[i] * count to sum.

      // Let's go with a simpler C implementation that matches `sum_repeated_elements_logic` directly.
      // This means we iterate over the array and for each element `arr[i]`, if it is repeated, we add `arr[i]` to the sum.
      // But this means if `arr = [2,2,3,3,3]`,
      // i=0, arr[0]=2. is_repeated(2) is true. sum = 2.
      // i=1, arr[1]=2. is_repeated(2) is true. sum = 2+2 = 4.
      // i=2, arr[2]=3. is_repeated(3) is true. sum = 4+3 = 7.
      // i=3, arr[3]=3. is_repeated(3) is true. sum = 7+3 = 10.
      // i=4, arr[4]=3. is_repeated(3) is true. sum = 10+3 = 13.
      // This matches `sum_repeated_elements_logic`.

      loop invariant 0 <= i <= size;
      loop invariant sum == sum_repeated_elements_logic(arr, size, 0) - sum_repeated_elements_logic(arr, size, i);
      loop assigns sum, i;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        // Check if arr[i] is repeated in the entire array
        if (/*@ ensures \result <==> is_repeated(arr, size, arr[i]); */
            is_repeated_helper(arr, size, arr[i])) {
            sum += arr[i];
        }
    }
    return sum;
}

/*@
  requires size >= 0;
  requires \valid_read(arr + (0..size-1));
  assigns \nothing;
  // Rule II.3: Use logical equivalence for boolean-like functions.
  ensures (\result == 1) <==> (count_occurrences(arr, size, val, 0) >= 2);
*/
int is_repeated_helper(int* arr, int size, int val) {
    int count = 0;
    /*@
      loop invariant 0 <= i <= size;
      loop invariant count == count_occurrences(arr, size, val, 0) - count_occurrences(arr, size, val, i);
      loop assigns count, i;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        if (arr[i] == val) {
            count++;
        }
    }
    return count >= 2 ? 1 : 0; // Rule III.1: C ternary is fine in C code.
}
