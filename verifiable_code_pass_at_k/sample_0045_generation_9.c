// Task ID: 45
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: int for booleans.

  // Axiomatic block for recursive GCD calculation over an array slice.
  axiomatic ArrayGCD {
    // Rule II.1: Recursive logic for complexity.
    // gcd_slice(arr, from, to) computes GCD of arr[from]...arr[to].
    logic integer gcd_slice{L}(int* arr, int from, int to);

    // Base case: GCD of a single element is the element itself.
    // Rule II.1: Base axiom.
    axiom gcd_slice_base{L}:
      \forall int* arr, integer i;
        gcd_slice(arr, i, i) == \abs(arr[i]);

    // Recursive case: GCD of a slice is GCD of the first element and the rest.
    // Rule II.1: Recursive axiom.
    axiom gcd_slice_rec{L}:
      \forall int* arr, integer from, integer to;
        from < to ==> gcd_slice(arr, from, to) == \gcd(\abs(arr[from]), gcd_slice(arr, from + 1, to));

    // Helper axiom: GCD is commutative and associative. This helps the prover with reordering.
    // This axiom is critical for proving properties of GCD over arrays.
    // Rule II.2: CRITICAL - Helper Axioms.
    axiom gcd_slice_order{L}:
      \forall int* arr, integer from, integer to, integer k;
        from <= k <= to ==> gcd_slice(arr, from, to) == \gcd(gcd_slice(arr, from, k), gcd_slice(arr, k + 1, to));

    // Helper axiom: GCD is non-negative.
    axiom gcd_slice_non_negative{L}:
      \forall int* arr, integer from, integer to;
        from <= to ==> gcd_slice(arr, from, to) >= 0;

    // Helper axiom: If an element is 0, it doesn't affect GCD unless all are 0.
    // \gcd(x, 0) == \abs(x)
    axiom gcd_slice_zero_element{L}:
      \forall int* arr, integer from, integer to, integer i;
        from <= i <= to && arr[i] == 0 ==> gcd_slice(arr, from, to) == gcd_slice(arr, from, i - 1) == \gcd(gcd_slice(arr, i + 1, to), \abs(arr[i]));
  }

  // Axiomatic block for standard GCD (Euclidean algorithm)
  axiomatic EuclideanGCD {
    logic integer \gcd(integer a, integer b);

    axiom gcd_positive_def:
      \forall integer a, b; \gcd(a, b) >= 0;

    axiom gcd_zero_a:
      \forall integer b; \gcd(0, b) == \abs(b);

    axiom gcd_zero_b:
      \forall integer a; \gcd(a, 0) == \abs(a);

    axiom gcd_recursive:
      \forall integer a, b; b != 0 ==> \gcd(a, b) == \gcd(b, a % b);

    // Rule II.2: CRITICAL - Helper Axioms for standard GCD.
    // These axioms help link the mathematical definition of GCD to its properties.
    axiom gcd_divides_a:
      \forall integer a, b; a != 0 || b != 0 ==> a % \gcd(a, b) == 0;

    axiom gcd_divides_b:
      \forall integer a, b; a != 0 || b != 0 ==> b % \gcd(a, b) == 0;

    axiom gcd_greatest:
      \forall integer a, b, d;
        d > 0 && a % d == 0 && b % d == 0 ==> d <= \gcd(a, b);
  }
*/

/*@
  // Rule II.5: Prevent runtime errors.
  // Array must not be null.
  requires arr != \null;
  // Array must have at least one element.
  requires n > 0;
  // All elements must be within int range. (Implicit by type, but good for clarity if array elements could be larger)
  // For safety, ensure that intermediate GCD calculations don't overflow,
  // though for positive integers, GCD is always less than or equal to min(\abs(a), \abs(b)).
  // If elements are int, their GCD will also be int.

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions (though this returns an int,
  // the principle of defining the result precisely applies).
  // The result of the function must be the GCD of the entire array slice.
  ensures \result == gcd_slice(arr, 0, n - 1);
  ensures \result >= 0; // GCD is conventionally non-negative.
*/
int find_array_gcd(int* arr, int n) {
    int result = arr[0];

    /*@
      loop invariant 0 <= i <= n;
      // The `result` variable at the start of each iteration `i` holds the GCD of `arr[0]` through `arr[i-1]`.
      // Rule II.4: Loop invariant.
      loop invariant (\forall integer k; 0 <= k < i ==> arr[k] % \abs(result) == 0);
      loop invariant \result == \gcd(\abs(arr[0]), gcd_slice(arr, 1, i - 1)); // This is equivalent to gcd_slice(arr, 0, i-1)

      // A more direct invariant for `result`:
      loop invariant i > 0 ==> \abs(result) == gcd_slice(arr, 0, i - 1);
      loop invariant i == 0 ==> \abs(result) == \abs(arr[0]); // Initial state before first iteration

      loop assigns result, i;
      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        // Calculate GCD of current result and the next array element.
        // Rule II.5: Prevent overflow. \gcd(int, int) result is within int range.
        // Use Euclidean algorithm's properties to ensure no overflow.
        // \abs(x) is fine.
        result = \gcd(\abs(result), \abs(arr[i]));
    }
    return result;
}
