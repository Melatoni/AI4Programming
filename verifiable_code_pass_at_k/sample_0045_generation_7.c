// Task ID: 45
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1, II.2: Recursive logic for complex properties.
  // Helper axiomatic block to define GCD for two integers.
  axiomatic GCD {
    logic integer gcd_recursive(integer a, integer b);

    axiom gcd_base:
      \forall integer a, b;
      a == 0 ==> gcd_recursive(a, b) == b;

    axiom gcd_recursive_step:
      \forall integer a, b;
      a > 0 ==> gcd_recursive(a, b) == gcd_recursive(b % a, a);

    // Helper axiom: GCD is commutative.
    axiom gcd_commutative:
      \forall integer a, b; gcd_recursive(a, b) == gcd_recursive(b, a);

    // Helper axiom: GCD of a number with itself is the number (for non-negative).
    axiom gcd_self:
      \forall integer a; a >= 0 ==> gcd_recursive(a, a) == a;

    // Helper axiom: GCD is non-negative.
    axiom gcd_non_negative:
      \forall integer a, b; gcd_recursive(a, b) >= 0;

    // Helper axiom: Divisibility property.
    axiom gcd_divisibility:
      \forall integer a, b, g;
      g == gcd_recursive(a, b) ==> (a % g == 0 && b % g == 0);

    // Helper axiom: Any common divisor divides the GCD.
    axiom gcd_greatest_common_divisor:
      \forall integer a, b, d;
      (a % d == 0 && b % d == 0) ==> (gcd_recursive(a, b) % d == 0);
  }
*/

/*@
  // Rule II.1, II.2: Recursive logic for GCD of an array.
  axiomatic ArrayGCD {
    logic integer array_gcd(int* a, integer n);

    axiom array_gcd_base:
      \forall int* a, integer n;
      n == 0 ==> array_gcd(a, n) == 0; // Or some other reasonable neutral element like 0 or 1.
                                      // Frama-C's WP usually prefers 0 for empty product/sum/gcd.

    axiom array_gcd_single:
      \forall int* a, integer n;
      n == 1 ==> array_gcd(a, n) == a[0];

    axiom array_gcd_recursive:
      \forall int* a, integer n;
      n > 1 ==> array_gcd(a, n) == gcd_recursive(a[n-1], array_gcd(a, n-1));

    // Helper axiom: GCD of array elements is non-negative if elements are non-negative.
    axiom array_gcd_non_negative:
      \forall int* a, integer n;
      (\forall integer i; 0 <= i < n ==> a[i] >= 0) ==> array_gcd(a, n) >= 0;

    // Helper axiom: Each element is divisible by the array GCD.
    axiom array_gcd_divisibility:
      \forall int* a, integer n, integer i;
      0 <= i < n ==> (a[i] % array_gcd(a, n) == 0);

    // Helper axiom: Any common divisor of all elements divides the array GCD.
    axiom array_gcd_greatest_common_divisor:
      \forall int* a, integer n, integer d;
      (\forall integer i; 0 <= i < n ==> a[i] % d == 0) ==> (array_gcd(a, n) % d == 0);
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent RTE. All array elements must be non-negative for GCD.
  requires \forall integer i; 0 <= i < n ==> a[i] >= 0;
  // Rule II.5: Prevent RTE. Ensure array access is valid.
  requires \valid_read(a + (0..n-1));

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions. Not applicable here as it returns an integer.
  // The result is the greatest common divisor of all elements in the array.
  // If n is 0, the GCD is conventionally 0.
  ensures \result == array_gcd(a, n);
*/
int find_array_gcd(int* a, int n) {
    if (n == 0) {
        return 0; // Conventional GCD of an empty set.
    }

    if (n == 1) {
        return a[0]; // GCD of a single element is the element itself.
    }

    int result = a[0];
    /*@
      loop invariant 1 <= i <= n;
      loop invariant result >= 0; // GCD is non-negative.
      // The `result` variable at each iteration `i` holds the GCD of `a[0]` through `a[i-1]`.
      loop invariant result == array_gcd(a, i);
      // Rule II.5: Prevent RTE.
      loop invariant \forall integer k; 0 <= k < i ==> a[k] % result == 0;

      loop assigns result, i;
      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        // Compute GCD of current result and next element using Euclidean algorithm.
        int x = result;
        int y = a[i];

        /*@
          loop invariant x >= 0 && y >= 0;
          // The invariant for the inner loop is that gcd_recursive(x, y) remains constant
          // and equals the GCD of the two numbers that entered this inner loop.
          loop invariant gcd_recursive(x, y) == gcd_recursive(result, a[i]);
          loop assigns x, y;
          // Rule II.4: Loop variant for termination.
          loop variant x;
        */
        while (x != 0) {
            int temp = x;
            x = y % x;
            y = temp;
        }
        result = y; // When x becomes 0, y holds the GCD.
    }
    return result;
}
