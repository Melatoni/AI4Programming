// Task ID: 41
// Generation: 9

/*@
  // Define an axiomatic block to simulate a lambda function for filtering even numbers.
  // This approach avoids actual function pointers which are not directly supported by WP.
  // Rule II.1: Recursive logic for complex properties.
  axiomatic EvenFilter {
    logic int is_even_lambda(int x);

    // Axiom: A number is even if it's divisible by 2.
    axiom is_even_def:
      \forall int x; is_even_lambda(x) == (x % 2 == 0 ? 1 : 0);
  }
*/

/*@
  requires N >= 0;
  // Rule II.5: Prevent potential overflow if elements are large and sum is computed.
  // Here, we constrain the array elements themselves to be within int range,
  // and the array size to prevent issues with indexing or loop bounds.
  // Assuming int is 32-bit, max value is 2^31 - 1.
  // If array elements are large, sum could overflow. This problem doesn't sum,
  // but it's a good practice to consider.
  requires \forall integer k; 0 <= k < N ==> -2147483648 <= arr[k] <= 2147483647;

  // Rule I.3: Array parameters decay to pointers.
  // `arr` is `int*` here because it's a 1D array.
  // `result_arr` is also `int*`.
  // `result_size_ptr` is `int*`.

  assigns result_arr[0..N-1], *result_size_ptr;

  // Rule II.3: Ensures clause for boolean-like functions (or functions that set a flag/size).
  // The result_size_ptr will point to the count of even numbers.
  // The result_arr will contain all even numbers from the input array, in order.
  ensures *result_size_ptr >= 0 && *result_size_ptr <= N;
  ensures \forall integer k; 0 <= k < *result_size_ptr ==> is_even_lambda(result_arr[k]) == 1;
  ensures \forall integer k; 0 <= k < *result_size_ptr ==>
    \exists integer i; 0 <= i < N && result_arr[k] == arr[i] && is_even_lambda(arr[i]) == 1;

  // Helper axiom for the ensures clause:
  // The number of even elements in result_arr is exactly the count of even elements in arr.
  ensures *result_size_ptr == (\sum integer i; 0 <= i < N && is_even_lambda(arr[i]) == 1; 1);

  // Helper axiom for the ensures clause:
  // The order of elements is preserved.
  // For any two elements in result_arr, if result_arr[k1] comes before result_arr[k2],
  // then the original index of result_arr[k1] in arr must be less than the original index of result_arr[k2].
  ensures \forall integer k1, k2; 0 <= k1 < k2 < *result_size_ptr ==>
    (\exists integer i1, i2; 0 <= i1 < i2 < N && result_arr[k1] == arr[i1] && result_arr[k2] == arr[i2]);
*/
void filter_even_numbers(int* arr, int N, int* result_arr, int* result_size_ptr) {
    int count = 0;
    /*@
      loop invariant 0 <= i <= N;
      loop invariant 0 <= count <= i;
      // All elements processed so far have been correctly filtered into result_arr.
      loop invariant \forall integer k; 0 <= k < count ==> is_even_lambda(result_arr[k]) == 1;
      loop invariant \forall integer k; 0 <= k < count ==>
        \exists integer p; 0 <= p < i && result_arr[k] == arr[p] && is_even_lambda(arr[p]) == 1;
      // The count accurately reflects the number of even elements found so far.
      loop invariant count == (\sum integer k; 0 <= k < i && is_even_lambda(arr[k]) == 1; 1);

      // The order of elements is preserved in result_arr.
      loop invariant \forall integer k1, k2; 0 <= k1 < k2 < count ==>
        (\exists integer i1, i2; 0 <= i1 < i2 < i && result_arr[k1] == arr[i1] && result_arr[k2] == arr[i2]);

      loop assigns i, count, result_arr[0..N-1]; // result_arr[0..count-1] is more precise but Frama-C needs a bound
      loop variant N - i;
    */
    for (int i = 0; i < N; ++i) {
        // Rule I.2: Using 1 for true, 0 for false.
        // Rule II.1: Using the axiomatic lambda function.
        if (is_even_lambda(arr[i]) == 1) { // Check if the number is even
            result_arr[count] = arr[i];
            count++;
        }
    }
    *result_size_ptr = count;
}
