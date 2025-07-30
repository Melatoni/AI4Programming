// Task ID: 38
// Generation: 4

/*@
  // Rule II.1: Define recursive logic functions for properties.
  // This axiomatic block defines a function to find the first even number in a given range of an array.
  axiomatic FirstEven {
    logic integer first_even_idx(int* arr, integer from, integer to);

    axiom first_even_idx_base:
      \forall int* arr, integer from, integer to;
      from > to ==> first_even_idx(arr, from, to) == -1; // -1 indicates not found

    axiom first_even_idx_recursive:
      \forall int* arr, integer from, integer to;
      from <= to ==> (
        (arr[from] % 2 == 0) ? (first_even_idx(arr, from, to) == from) : (first_even_idx(arr, from, to) == first_even_idx(arr, from + 1, to))
      );
  }

  // This axiomatic block defines a function to find the first odd number in a given range of an array.
  axiomatic FirstOdd {
    logic integer first_odd_idx(int* arr, integer from, integer to);

    axiom first_odd_idx_base:
      \forall int* arr, integer from, integer to;
      from > to ==> first_odd_idx(arr, from, to) == -1; // -1 indicates not found

    axiom first_odd_idx_recursive:
      \forall int* arr, integer from, integer to;
      from <= to ==> (
        (arr[from] % 2 != 0) ? (first_odd_idx(arr, from, to) == from) : (first_odd_idx(arr, from, to) == first_odd_idx(arr, from + 1, to))
      );
  }
*/

/*@
  requires n > 0;
  requires \valid_read(arr + (0..n-1));
  
  // Rule II.5: Prevent division by zero.
  // The first odd number must exist and not be zero.
  requires first_odd_idx(arr, 0, n - 1) != -1;
  requires arr[first_odd_idx(arr, 0, n - 1)] != 0;

  // The first even number must exist.
  requires first_even_idx(arr, 0, n - 1) != -1;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The result is 1 if the division is possible and performed, 0 otherwise.
  // The function returns 1 if both first even and first odd numbers are found
  // AND the first odd number is not zero.
  // The result `res` will hold the division if successful.
  ensures (first_even_idx(arr, 0, n - 1) != -1 &&
           first_odd_idx(arr, 0, n - 1) != -1 &&
           arr[first_odd_idx(arr, 0, n - 1)] != 0)
          ==> (\result == (double)arr[first_even_idx(arr, 0, n - 1)] / arr[first_odd_idx(arr, 0, n - 1)]);
  ensures !(first_even_idx(arr, 0, n - 1) != -1 &&
            first_odd_idx(arr, 0, n - 1) != -1 &&
            arr[first_odd_idx(arr, 0, n - 1)] != 0)
           ==> \result == -1.0; // Indicate error by returning -1.0
*/
double find_division_first_even_odd(int* arr, int n) {
    int first_even = -1;
    int first_odd = -1;
    int i = 0;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i && arr[k] % 2 == 0 ==> first_even != -1 && first_even == \at(first_even, LoopEntry);
      loop invariant \forall integer k; 0 <= k < i && arr[k] % 2 != 0 ==> first_odd != -1 && first_odd == \at(first_odd, LoopEntry);
      
      // If first_even is found, it must be the first one up to current i.
      loop invariant (first_even != -1) ==> (first_even == first_even_idx(arr, 0, i-1));
      // If first_odd is found, it must be the first one up to current i.
      loop invariant (first_odd != -1) ==> (first_odd == first_odd_idx(arr, 0, i-1));

      // If first_even is not found, no even number exists up to current i.
      loop invariant (first_even == -1) ==> (\forall integer k; 0 <= k < i ==> arr[k] % 2 != 0);
      // If first_odd is not found, no odd number exists up to current i.
      loop invariant (first_odd == -1) ==> (\forall integer k; 0 <= k < i ==> arr[k] % 2 == 0);

      loop assigns i, first_even, first_odd;
      loop variant n - i;
    */
    while (i < n) {
        if (first_even == -1 && arr[i] % 2 == 0) {
            first_even = arr[i];
        }
        if (first_odd == -1 && arr[i] % 2 != 0) {
            first_odd = arr[i];
        }
        // Optimization: if both are found, we can break early.
        // This is a common pattern for "first occurrence" searches.
        if (first_even != -1 && first_odd != -1) {
            break;
        }
        i++;
    }

    if (first_even != -1 && first_odd != -1 && first_odd != 0) {
        return (double)first_even / first_odd;
    } else {
        return -1.0; // Indicate error
    }
}
