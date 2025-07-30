// Task ID: 45
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in axiomatic blocks.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic GCD {
    logic integer gcd(integer a, integer b);

    axiom gcd_base_a:
      \forall integer a; a > 0 ==> gcd(a, 0) == a;

    axiom gcd_base_b:
      \forall integer b; b > 0 ==> gcd(0, b) == b;

    axiom gcd_recursive:
      \forall integer a, b; a > 0 && b > 0 ==> gcd(a, b) == gcd(b, a % b);

    // Helper axiom for properties of gcd, e.g., gcd is commutative
    axiom gcd_commutative:
      \forall integer a, b; gcd(a, b) == gcd(b, a);

    // Helper axiom: gcd(a,b) divides a and b
    axiom gcd_divides_a:
      \forall integer a, b; a >= 0 && b >= 0 && (a > 0 || b > 0) ==> a % gcd(a,b) == 0;
    axiom gcd_divides_b:
      \forall integer a, b; a >= 0 && b >= 0 && (a > 0 || b > 0) ==> b % gcd(a,b) == 0;

    // Helper axiom: if c divides a and b, then c divides gcd(a,b)
    axiom gcd_greatest:
      \forall integer a, b, c; a >= 0 && b >= 0 && c > 0 && a % c == 0 && b % c == 0 ==> gcd(a,b) % c == 0;

    // Recursive logic for GCD of an array segment
    logic integer array_gcd(int* a, integer from, integer to);

    axiom array_gcd_single:
      \forall int* a, integer i; array_gcd(a, i, i) == a[i];

    axiom array_gcd_recursive:
      \forall int* a, integer from, integer to;
        from < to ==> array_gcd(a, from, to) == gcd(a[from], array_gcd(a, from + 1, to));

    // Helper axiom: array_gcd is positive if elements are positive
    axiom array_gcd_positive:
      \forall int* a, integer from, integer to;
        from <= to && (\forall integer k; from <= k <= to ==> a[k] > 0) ==> array_gcd(a, from, to) > 0;

    // Helper axiom: array_gcd divides all elements in the range
    axiom array_gcd_divides_all:
      \forall int* a, integer from, integer to, integer k;
        from <= to && from <= k <= to && a[k] > 0 ==> a[k] % array_gcd(a, from, to) == 0;
  }
*/

/*@
  requires a >= 0;
  requires b >= 0;
  assigns \nothing;
  ensures \result == gcd(a, b);
  // Rule II.5: Prevent Runtime Errors (RTE)
  // For recursive calls, ensure arguments remain non-negative.
  // This function is implemented iteratively, so no stack overflow.
*/
int find_gcd(int a, int b) {
    /*@
      loop invariant a >= 0 && b >= 0;
      loop invariant gcd(a, b) == gcd(\at(a,Pre), \at(b,Pre));
      loop assigns a, b;
      loop variant a + b; // Or just a, or just b, since one gets smaller
    */
    while (b != 0) {
        int temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

/*@
  requires n > 0;
  requires \valid_read(arr + (0..n-1));
  // Rule II.5: Prevent Runtime Errors (RTE)
  // Ensure all array elements are positive for GCD definition to be well-behaved
  // and to prevent infinite loops if an element is 0.
  requires \forall integer i; 0 <= i < n ==> arr[i] > 0;
  assigns \nothing;
  ensures \result == array_gcd(arr, 0, n - 1);
*/
int find_array_gcd(int* arr, int n) {
    int result = arr[0];
    /*@
      loop invariant 1 <= i <= n;
      loop invariant result > 0;
      loop invariant result == array_gcd(arr, 0, i - 1);
      loop assigns result, i;
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        result = find_gcd(result, arr[i]);
    }
    return result;
}
