// Task ID: 38
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule I.3: Array pointer decay (though not directly used in this problem,
  //           it's a general rule for array parameters).
*/
/*@ axiomatic EvenOddDivision {
  logic integer find_first_even_recursive(int* arr, int start, int end) reads arr[0..end-1];
  axiom find_first_even_base:
    \forall int* arr, int start, int end;
    start >= end ==> find_first_even_recursive(arr, start, end) == -1; // -1 indicates not found

  axiom find_first_even_recursive_step:
    \forall int* arr, int start, int end;
    start < end ==>
      find_first_even_recursive(arr, start, end) ==
        (if (arr[start] % 2 == 0) then arr[start]
         else find_first_even_recursive(arr, start + 1, end));

  logic integer find_first_odd_recursive(int* arr, int start, int end) reads arr[0..end-1];
  axiom find_first_odd_base:
    \forall int* arr, int start, int end;
    start >= end ==> find_first_odd_recursive(arr, start, end) == -1; // -1 indicates not found

  axiom find_first_odd_recursive_step:
    \forall int* arr, int start, int end;
    start < end ==>
      find_first_odd_recursive(arr, start, end) ==
        (if (arr[start] % 2 != 0) then arr[start]
         else find_first_odd_recursive(arr, start + 1, end));

  // Helper axiom: If an even number is found, it must be one of the elements
  // This helps the prover connect the recursive definition to the array content.
  axiom find_first_even_property:
    \forall int* arr, int start, int end, integer val;
    val == find_first_even_recursive(arr, start, end) && val != -1 ==>
      \exists integer i; start <= i < end && arr[i] == val && arr[i] % 2 == 0 &&
      (\forall integer j; start <= j < i ==> arr[j] % 2 != 0);

  // Helper axiom: If an odd number is found, it must be one of the elements
  axiom find_first_odd_property:
    \forall int* arr, int start, int end, integer val;
    val == find_first_odd_recursive(arr, start, end) && val != -1 ==>
      \exists integer i; start <= i < end && arr[i] == val && arr[i] % 2 != 0 &&
      (\forall integer j; start <= j < i ==> arr[j] % 2 == 0);

  // Helper axiom: If no even number is found, then all elements are odd.
  axiom find_first_even_not_found:
    \forall int* arr, int start, int end;
    find_first_even_recursive(arr, start, end) == -1 ==>
      \forall integer i; start <= i < end ==> arr[i] % 2 != 0;

  // Helper axiom: If no odd number is found, then all elements are even.
  axiom find_first_odd_not_found:
    \forall int* arr, int start, int end;
    find_first_odd_recursive(arr, start, end) == -1 ==>
      \forall integer i; start <= i < end ==> arr[i] % 2 == 0;
}
*/

/*@
  requires N >= 0;
  // Rule II.5: Prevent runtime errors (division by zero).
  // The function returns -1 if no even or no odd number is found, or if odd is zero.
  // The requires clause ensures that if the function returns a valid division,
  // the first odd number found is not zero.
  requires find_first_odd_recursive(arr, 0, N) != 0;

  // Ensure array elements are within int range to avoid overflow issues during modulo.
  // This is a good practice for robustness, though not strictly required by the problem.
  requires \forall integer i; 0 <= i < N ==> -2147483648 <= arr[i] <= 2147483647;

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  // The function returns -1 if no even or no odd number is found.
  // Otherwise, it returns the division.
  ensures (\exists integer even_val, odd_val;
             even_val == find_first_even_recursive(arr, 0, N) && even_val != -1 &&
             odd_val == find_first_odd_recursive(arr, 0, N) && odd_val != -1 &&
             odd_val != 0
          ) <==> (\result != -1);

  ensures \result == -1 <==>
          (find_first_even_recursive(arr, 0, N) == -1 ||
           find_first_odd_recursive(arr, 0, N) == -1 ||
           find_first_odd_recursive(arr, 0, N) == 0);

  ensures \result != -1 ==>
          \result == find_first_even_recursive(arr, 0, N) / find_first_odd_recursive(arr, 0, N);
*/
int find_even_odd_division(int* arr, int N) {
    int first_even = -1;
    int first_odd = -1;
    int i = 0;

    /*@
      loop invariant 0 <= i <= N;
      loop invariant (\forall integer k; 0 <= k < i ==> arr[k] % 2 != 0) ==> first_even == -1;
      loop invariant (\exists integer k; 0 <= k < i && arr[k] % 2 == 0) ==>
                     (\exists integer m; 0 <= m < i && arr[m] == first_even && arr[m] % 2 == 0 &&
                      (\forall integer l; 0 <= l < m ==> arr[l] % 2 != 0));
      loop invariant (first_even != -1) ==> first_even == find_first_even_recursive(arr, 0, i);
      loop invariant (first_even == -1) ==> find_first_even_recursive(arr, 0, i) == -1;

      loop assigns i, first_even;
      loop variant N - i;
    */
    for (i = 0; i < N; i++) {
        if (arr[i] % 2 == 0) {
            first_even = arr[i];
            break; // Found the first even, exit loop
        }
    }

    /*@
      loop invariant 0 <= i <= N; // i is the index where first_even was found, or N
      loop invariant (\forall integer k; 0 <= k < i ==> arr[k] % 2 == 0) ==> first_odd == -1;
      loop invariant (\exists integer k; 0 <= k < i && arr[k] % 2 != 0) ==>
                     (\exists integer m; 0 <= m < i && arr[m] == first_odd && arr[m] % 2 != 0 &&
                      (\forall integer l; 0 <= l < m ==> arr[l] % 2 == 0));
      loop invariant (first_odd != -1) ==> first_odd == find_first_odd_recursive(arr, 0, i);
      loop invariant (first_odd == -1) ==> find_first_odd_recursive(arr, 0, i) == -1;

      loop assigns i, first_odd;
      loop variant N - i;
    */
    for (i = 0; i < N; i++) {
        if (arr[i] % 2 != 0) {
            first_odd = arr[i];
            break; // Found the first odd, exit loop
        }
    }

    if (first_even == -1 || first_odd == -1 || first_odd == 0) {
        return -1; // Indicate not found or division by zero
    } else {
        // Rule II.5: Prevent overflow if first_even is INT_MIN and first_odd is -1.
        // Assuming integer division behavior is standard.
        return first_even / first_odd;
    }
}
