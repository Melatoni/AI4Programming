// Task ID: 38
// Generation: 2

/*@
  // Rule II.1, II.2: Define axiomatic for finding the first even/odd number.
  // We need these to formally define the properties of the result.

  axiomatic FindNumbers {
    logic integer first_even_val(int* arr, integer n);
    logic integer first_even_idx(int* arr, integer n);

    axiom first_even_val_def:
      \forall int* arr, integer n;
      (first_even_idx(arr, n) == -1) ==> (first_even_val(arr, n) == -1);

    axiom first_even_val_exists:
      \forall int* arr, integer n;
      (first_even_idx(arr, n) != -1) ==> (first_even_val(arr, n) == arr[first_even_idx(arr, n)]);

    axiom first_even_idx_def_exists:
      \forall int* arr, integer n;
      (0 <= n && \exists integer k; 0 <= k < n && arr[k] % 2 == 0) ==>
      (0 <= first_even_idx(arr, n) < n && arr[first_even_idx(arr, n)] % 2 == 0 &&
       \forall integer j; 0 <= j < first_even_idx(arr, n) ==> arr[j] % 2 != 0);

    axiom first_even_idx_def_not_exists:
      \forall int* arr, integer n;
      (0 <= n && \forall integer k; 0 <= k < n ==> arr[k] % 2 != 0) ==>
      (first_even_idx(arr, n) == -1);

    logic integer first_odd_val(int* arr, integer n);
    logic integer first_odd_idx(int* arr, integer n);

    axiom first_odd_val_def:
      \forall int* arr, integer n;
      (first_odd_idx(arr, n) == -1) ==> (first_odd_val(arr, n) == -1);

    axiom first_odd_val_exists:
      \forall int* arr, integer n;
      (first_odd_idx(arr, n) != -1) ==> (first_odd_val(arr, n) == arr[first_odd_idx(arr, n)]);

    axiom first_odd_idx_def_exists:
      \forall int* arr, integer n;
      (0 <= n && \exists integer k; 0 <= k < n && arr[k] % 2 != 0) ==>
      (0 <= first_odd_idx(arr, n) < n && arr[first_odd_idx(arr, n)] % 2 != 0 &&
       \forall integer j; 0 <= j < first_odd_idx(arr, n) ==> arr[j] % 2 == 0);

    axiom first_odd_idx_def_not_exists:
      \forall int* arr, integer n;
      (0 <= n && \forall integer k; 0 <= k < n ==> arr[k] % 2 == 0) ==>
      (first_odd_idx(arr, n) == -1);
  }
*/

/*@
  requires n >= 0;
  requires \valid_read_array(arr, n);

  // Rule II.5: Prevent division by zero.
  // The first odd number must exist and not be zero.
  requires first_odd_val(arr, n) != -1 && first_odd_val(arr, n) != 0;

  // The first even number must exist.
  requires first_even_val(arr, n) != -1;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for the result.
  // The result is the division if both numbers are found and odd is not zero.
  ensures \result == first_even_val(arr, n) / first_odd_val(arr, n);
*/
int find_division_first_even_odd(int* arr, int n) { // Rule I.2: Use int for bool-like values if needed, but not here.
    int firstEven = -1;
    int firstOdd = -1;
    int i = 0;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant (firstEven == -1) <==> (\forall integer k; 0 <= k < i ==> arr[k] % 2 != 0);
      loop invariant (firstEven != -1) ==> (0 <= first_even_idx(arr, i) < i && arr[first_even_idx(arr, i)] % 2 == 0 &&
                                            \forall integer j; 0 <= j < first_even_idx(arr, i) ==> arr[j] % 2 != 0);
      loop invariant (firstOdd == -1) <==> (\forall integer k; 0 <= k < i ==> arr[k] % 2 == 0);
      loop invariant (firstOdd != -1) ==> (0 <= first_odd_idx(arr, i) < i && arr[first_odd_idx(arr, i)] % 2 != 0 &&
                                           \forall integer j; 0 <= j < first_odd_idx(arr, i) ==> arr[j] % 2 == 0);
      loop assigns i, firstEven, firstOdd;
      loop variant n - i;
    */
    while (i < n) {
        if (firstEven == -1 && arr[i] % 2 == 0) {
            firstEven = arr[i];
        }
        if (firstOdd == -1 && arr[i] % 2 != 0) {
            firstOdd = arr[i];
        }
        // Optimization: if both are found, we can break early.
        // This is not strictly necessary for correctness but good for performance.
        // Frama-C WP can handle this.
        if (firstEven != -1 && firstOdd != -1) {
            break;
        }
        i++;
    }

    // According to the requires clauses, both firstEven and firstOdd will be found
    // and firstOdd will not be zero.
    return firstEven / firstOdd;
}
