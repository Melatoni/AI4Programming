// Task ID: 38
// Generation: 1

/*@
  // Rule II.1: Define recursive logic functions for properties over sequences.
  // This axiomatic block defines what it means for a number to be even or odd,
  // and how to find the first even/odd number in a given range of an array.
  axiomatic EvenOddProperties {
    logic boolean is_even(integer x) = x % 2 == 0;
    logic boolean is_odd(integer x) = x % 2 != 0;

    // Rule I.3: Array parameters in logic functions must use the correct pointer type.
    // first_even(arr, from, to) finds the first even number in arr[from..to].
    logic integer first_even{L}(int *arr, integer from, integer to)
      reads arr[from..to];

    axiom first_even_base_even{L}:
      \forall int *arr, integer from, to;
        from <= to && is_even(arr[from]) ==> first_even(arr, from, to) == arr[from];

    axiom first_even_base_no_even{L}:
      \forall int *arr, integer from, to;
        from <= to && !is_even(arr[from]) && from == to ==> first_even(arr, from, to) == -1; // Sentinel for not found

    axiom first_even_recursive{L}:
      \forall int *arr, integer from, to;
        from < to && !is_even(arr[from]) ==> first_even(arr, from, to) == first_even(arr, from + 1, to);

    // Rule II.2: Helper axiom for first_even to ensure if one exists, it's positive.
    // Assuming array elements are positive.
    axiom first_even_positive{L}:
      \forall int *arr, integer from, to;
        (\exists integer k; from <= k <= to && is_even(arr[k])) ==> first_even(arr, from, to) >= 0;

    // first_odd(arr, from, to) finds the first odd number in arr[from..to].
    logic integer first_odd{L}(int *arr, integer from, integer to)
      reads arr[from..to];

    axiom first_odd_base_odd{L}:
      \forall int *arr, integer from, to;
        from <= to && is_odd(arr[from]) ==> first_odd(arr, from, to) == arr[from];

    axiom first_odd_base_no_odd{L}:
      \forall int *arr, integer from, to;
        from <= to && !is_odd(arr[from]) && from == to ==> first_odd(arr, from, to) == -1; // Sentinel for not found

    axiom first_odd_recursive{L}:
      \forall int *arr, integer from, to;
        from < to && !is_odd(arr[from]) ==> first_odd(arr, from + 1, to) == first_odd(arr, from, to);

    // Rule II.2: Helper axiom for first_odd to ensure if one exists, it's positive.
    // Assuming array elements are positive.
    axiom first_odd_positive{L}:
      \forall int *arr, integer from, to;
        (\exists integer k; from <= k <= to && is_odd(arr[k])) ==> first_odd(arr, from, to) >= 0;
  }

  // Helper logic function to check if an element is present in the array.
  logic boolean is_present{L}(int *arr, integer size, integer val)
    reads arr[0..size-1];

  axiom is_present_base{L}:
    \forall int *arr, integer size, val;
      size > 0 && arr[0] == val ==> is_present(arr, size, val);

  axiom is_present_recursive{L}:
    \forall int *arr, integer size, val;
      size > 0 && arr[0] != val ==> is_present(arr+1, size-1, val) == is_present(arr, size, val);

  axiom is_present_empty{L}:
    \forall int *arr, integer val;
      is_present(arr, 0, val) == \false;
*/

/*@
  requires size > 0;
  // All elements must be non-negative. This is crucial for the -1 sentinel value.
  requires \forall integer i; 0 <= i < size ==> arr[i] >= 0;

  // Pre-conditions for the existence of first even and odd numbers:
  // We need at least one even number and one odd number for the division to be meaningful.
  // Also, the first odd number must not be zero to avoid division by zero.
  requires (\exists integer i; 0 <= i < size && is_even(arr[i]));
  requires (\exists integer i; 0 <= i < size && is_odd(arr[i]));
  requires first_odd(arr, 0, size - 1) != 0;

  assigns \nothing;

  // Ensures clause: The result is the division of the first even by the first odd.
  // Rule II.3: For boolean-like results, use logical equivalence. Here, the result
  // is a float, but we ensure its value precisely.
  ensures \result == (double)first_even(arr, 0, size - 1) / first_odd(arr, 0, size - 1);
*/
double find_first_even_odd_division(int *arr, int size) {
    int first_even_val = -1;
    int first_odd_val = -1;

    /*@
      loop invariant 0 <= i <= size;
      loop invariant first_even_val == (if (\exists integer k; 0 <= k < i && is_even(arr[k]))
                                        then first_even(arr, 0, i - 1)
                                        else -1);
      loop invariant first_odd_val == (if (\exists integer k; 0 <= k < i && is_odd(arr[k]))
                                       then first_odd(arr, 0, i - 1)
                                       else -1);
      loop invariant \forall integer k; 0 <= k < i && is_even(arr[k]) ==> first_even_val != -1;
      loop invariant \forall integer k; 0 <= k < i && is_odd(arr[k]) ==> first_odd_val != -1;

      loop assigns i, first_even_val, first_odd_val;
      loop variant size - i; // Rule II.4: Mandatory loop variant.
    */
    for (int i = 0; i < size; i++) {
        if (first_even_val == -1 && arr[i] % 2 == 0) {
            first_even_val = arr[i];
        }
        if (first_odd_val == -1 && arr[i] % 2 != 0) {
            first_odd_val = arr[i];
        }
        // Optimization: if both found, no need to continue
        if (first_even_val != -1 && first_odd_val != -1) {
            break;
        }
    }

    // The required clauses guarantee that first_even_val and first_odd_val
    // will not be -1 here, and first_odd_val will not be 0.
    // The cast to double is necessary for floating-point division.
    return (double)first_even_val / first_odd_val;
}
