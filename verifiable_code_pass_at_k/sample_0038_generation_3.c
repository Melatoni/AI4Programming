// Task ID: 38
// Generation: 3

/*@
  // Rule II.1: Define recursive logic function for finding the first even number.
  axiomatic FirstEven {
    logic integer first_even_idx(int* a, integer n);

    axiom first_even_idx_base:
      \forall int* a, integer n; n <= 0 ==> first_even_idx(a, n) == -1;

    axiom first_even_idx_rec_even:
      \forall int* a, integer n; n > 0 && a[0] % 2 == 0 ==> first_even_idx(a, n) == 0;

    axiom first_even_idx_rec_odd:
      \forall int* a, integer n; n > 0 && a[0] % 2 != 0 ==> first_even_idx(a, n) ==
        (first_even_idx(a + 1, n - 1) == -1 ? -1 : first_even_idx(a + 1, n - 1) + 1);
  }
*/

/*@
  // Rule II.1: Define recursive logic function for finding the first odd number.
  axiomatic FirstOdd {
    logic integer first_odd_idx(int* a, integer n);

    axiom first_odd_idx_base:
      \forall int* a, integer n; n <= 0 ==> first_odd_idx(a, n) == -1;

    axiom first_odd_idx_rec_odd:
      \forall int* a, integer n; n > 0 && a[0] % 2 != 0 ==> first_odd_idx(a, n) == 0;

    axiom first_odd_idx_rec_even:
      \forall int* a, integer n; n > 0 && a[0] % 2 == 0 ==> first_odd_idx(a, n) ==
        (first_odd_idx(a + 1, n - 1) == -1 ? -1 : first_odd_idx(a + 1, n - 1) + 1);
  }
*/

/*@
  requires n > 0;
  requires \valid_read_range(arr, 0, n - 1);

  // Rule II.5: Prevent division by zero.
  requires first_odd_idx(arr, n) != -1;
  requires arr[first_odd_idx(arr, n)] != 0;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  ensures \result == (real)arr[first_even_idx(arr, n)] / arr[first_odd_idx(arr, n)];
*/
double find_division_first_even_odd(int* arr, int n) {
    int first_even = -1;
    int first_odd = -1;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant (first_even == -1) <==> (\forall integer k; 0 <= k < i ==> arr[k] % 2 != 0);
      loop invariant (first_even != -1) ==> (\exists integer k; 0 <= k < i && arr[k] % 2 == 0 && first_even == arr[k]);
      loop invariant (first_odd == -1) <==> (\forall integer k; 0 <= k < i ==> arr[k] % 2 == 0);
      loop invariant (first_odd != -1) ==> (\exists integer k; 0 <= k < i && arr[k] % 2 != 0 && first_odd == arr[k]);

      // Ensure that if a first even/odd is found, it's the *first* one
      loop invariant (first_even != -1) ==> (\forall integer k; 0 <= k < i && arr[k] == first_even ==> (\forall integer j; 0 <= j < k ==> arr[j] % 2 != 0));
      loop invariant (first_odd != -1) ==> (\forall integer k; 0 <= k < i && arr[k] == first_odd ==> (\forall integer j; 0 <= j < k ==> arr[j] % 2 == 0));

      loop assigns i, first_even, first_odd;
      loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        if (first_even == -1 && arr[i] % 2 == 0) {
            first_even = arr[i];
        }
        if (first_odd == -1 && arr[i] % 2 != 0) {
            first_odd = arr[i];
        }
        if (first_even != -1 && first_odd != -1) {
            break;
        }
    }

    // These checks are ensured by the function's requires clause, but included for clarity.
    // assert first_even != -1; // Guaranteed by the problem description (implicitly, that such numbers exist if division is possible)
    // assert first_odd != -1;
    // assert first_odd != 0; // Guaranteed by requires

    return (double)first_even / first_odd;
}
