// Task ID: 45
// Generation: 5

/*@
  // Axiomatic block for GCD helper functions
  axiomatic GCD {
    /*@
      logic integer gcd_recursive(integer a, integer b) =
        // Rule III.2: No parentheses around if-then-else
        // Rule III.1: No C-style ternary
        if b == 0 then a
        else gcd_recursive(b, a % b);

      // Helper axiom for gcd_recursive: GCD is commutative
      axiom gcd_commutative:
        \forall integer a, b; gcd_recursive(a, b) == gcd_recursive(b, a);

      // Helper axiom for gcd_recursive: GCD with 0
      axiom gcd_zero_left:
        \forall integer a; gcd_recursive(0, a) == a;

      // Helper axiom for gcd_recursive: GCD with 0
      axiom gcd_zero_right:
        \forall integer a; gcd_recursive(a, 0) == a;

      // Helper axiom for gcd_recursive: GCD divides both numbers
      axiom gcd_divides:
        \forall integer a, b;
          (a % gcd_recursive(a, b) == 0) && (b % gcd_recursive(a, b) == 0);

      // Helper axiom for gcd_recursive: GCD is the greatest common divisor
      axiom gcd_greatest:
        \forall integer a, b, d;
          (a % d == 0 && b % d == 0) ==> (d <= gcd_recursive(a, b));

      // Rule II.1: Recursive logic for array GCD
      logic integer array_gcd{L}(int* arr, integer from, integer to) =
        if from > to then 0 // Base case: empty range, GCD is 0 (or undefined, but 0 works for cumulative GCD)
        else if from == to then arr[from]
        else gcd_recursive(arr[from], array_gcd{L}(arr, from + 1, to));

      // Helper axiom: array_gcd property for a single element
      axiom array_gcd_single:
        \forall int* arr, integer i;
          array_gcd(arr, i, i) == arr[i];

      // Helper axiom: array_gcd property for two elements
      axiom array_gcd_two:
        \forall int* arr, integer i, j;
          i < j ==> array_gcd(arr, i, j) == gcd_recursive(arr[i], array_gcd(arr, i + 1, j));

      // Helper axiom: array_gcd property for reversed range (commutative property)
      axiom array_gcd_reversed:
        \forall int* arr, integer from, to;
          from <= to ==> array_gcd(arr, from, to) == array_gcd(arr, to, from);

      // Helper axiom: array_gcd property for concatenation
      axiom array_gcd_concat:
        \forall int* arr, integer from, mid, to;
          from <= mid <= to ==> array_gcd(arr, from, to) == gcd_recursive(array_gcd(arr, from, mid), array_gcd(arr, mid + 1, to));
    */
  }
*/


/*@
  requires N > 0;
  requires \valid_read_range(arr, 0, N - 1);
  // All elements must be non-negative for GCD properties to hold as typically defined.
  // We assume here that the input array elements are non-negative.
  requires \forall integer k; 0 <= k < N ==> arr[k] >= 0;

  assigns \nothing;

  ensures \result == gcd_recursive(arr[0], array_gcd(arr, 1, N - 1));
  ensures \result == array_gcd(arr, 0, N - 1);
  ensures \result >= 0; // GCD is always non-negative
  ensures \forall integer k; 0 <= k < N ==> arr[k] % \result == 0; // The result divides all elements
  ensures \forall integer d; (\forall integer k; 0 <= k < N ==> arr[k] % d == 0) ==> (d <= \result); // The result is the greatest common divisor
*/
int find_gcd_of_array(int* arr, int N) {
    // Base case: if array has only one element, its GCD is itself
    if (N == 1) {
        return arr[0];
    }

    int result = arr[0]; // Initialize result with the first element

    /*@
      loop invariant 1 <= i <= N;
      // The `result` variable at iteration `i` holds the GCD of `arr[0]` to `arr[i-1]`.
      loop invariant result == array_gcd(arr, 0, i - 1);
      // All elements processed so far are divisible by the current `result`.
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] % result == 0;
      // The current `result` value is the greatest common divisor of elements processed so far.
      loop invariant \forall integer d; (\forall integer k; 0 <= k < i ==> arr[k] % d == 0) ==> (d <= result);

      loop assigns i, result;
      loop variant N - i;
    */
    for (int i = 1; i < N; i++) {
        // Euclidean algorithm for GCD: gcd(a, b) = gcd(b, a % b)
        // We need to implement this iteratively or recursively.
        // For simplicity and direct verifiability, we'll use a nested loop for the Euclidean algorithm.
        // Alternatively, we could call a helper function for gcd(a, b). For this problem,
        // we will inline the Euclidean algorithm.

        int a = result;
        int b = arr[i];

        /*@
          loop invariant \forall integer k; 0 <= k < i ==> arr[k] % a == 0;
          loop invariant \forall integer k; 0 <= k < i ==> arr[k] % b == 0;
          loop invariant gcd_recursive(a, b) == gcd_recursive(\at(result, LoopEntry), \at(arr[i], LoopEntry));
          loop invariant a >= 0;
          loop invariant b >= 0;
          loop assigns a, b;
          loop variant b;
        */
        while (b != 0) {
            int temp = b;
            b = a % b;
            a = temp;
        }
        result = a; // `a` now holds the GCD of the previous `result` and `arr[i]`
    }

    return result;
}
