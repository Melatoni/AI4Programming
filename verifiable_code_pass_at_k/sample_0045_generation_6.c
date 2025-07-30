// Task ID: 45
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay (not applicable here, but keep in mind).
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
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
      \forall integer a; gcd(a, 0) == \abs(a);

    axiom gcd_base_b:
      \forall integer b; gcd(0, b) == \abs(b);

    axiom gcd_recursive:
      \forall integer a, b;
        a != 0 && b != 0 ==> gcd(a, b) == gcd(b, a % b);

    // Helper axiom for positive inputs, simplifies reasoning
    axiom gcd_positive:
      \forall integer a, b; a >= 0 && b >= 0 ==> gcd(a, b) >= 0;

    // Helper axiom for common divisor property
    axiom gcd_divides_a:
      \forall integer a, b; gcd(a, b) != 0 ==> a % gcd(a, b) == 0;

    axiom gcd_divides_b:
      \forall integer a, b; gcd(a, b) != 0 ==> b % gcd(a, b) == 0;

    // Helper axiom for greatest common divisor property
    axiom gcd_greatest_common_divisor:
      \forall integer a, b, d;
        d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a, b);
  }
*/

/*@
  requires a >= 0 && b >= 0; // Ensure non-negative inputs for simpler reasoning with gcd axiom
  assigns \nothing;
  ensures \result == gcd(a, b);
*/
int calculate_gcd(int a, int b) {
    /*@
      loop invariant a_val >= 0 && b_val >= 0;
      loop invariant gcd(a_val, b_val) == gcd(a, b);
      loop assigns a_val, b_val;
      loop variant a_val + b_val; // Sum of values decreases
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
  requires \forall integer i; 0 <= i < n ==> arr[i] >= 0; // All elements must be non-negative
  
  // Rule II.5: Prevent overflow if intermediate GCDs grow large.
  // The maximum possible GCD is the maximum element itself.
  // Assuming int can hold the maximum element.
  // No specific overflow check needed for GCD itself as it reduces values.

  assigns \nothing;

  // Define the GCD of an array recursively using a logic function
  axiomatic ArrayGCD {
    logic integer array_gcd(int* arr, integer n);

    axiom array_gcd_base:
      \forall int* arr; array_gcd(arr, 1) == arr[0];

    axiom array_gcd_recursive:
      \forall int* arr, integer n;
        n > 1 ==> array_gcd(arr, n) == gcd(arr[n-1], array_gcd(arr, n-1));

    // Helper axiom: array_gcd is non-negative if all elements are non-negative
    axiom array_gcd_non_negative:
      \forall int* arr, integer n;
        n > 0 && (\forall integer i; 0 <= i < n ==> arr[i] >= 0) ==> array_gcd(arr, n) >= 0;

    // Helper axiom: array_gcd divides all elements
    axiom array_gcd_divides_all:
      \forall int* arr, integer n, integer i;
        n > 0 && 0 <= i < n && (\forall integer k; 0 <= k < n ==> arr[k] >= 0) ==> arr[i] % array_gcd(arr, n) == 0;

    // Helper axiom: array_gcd is the greatest common divisor
    axiom array_gcd_is_greatest:
      \forall int* arr, integer n, integer d;
        n > 0 && d > 0 && (\forall integer i; 0 <= i < n ==> arr[i] >= 0 && arr[i] % d == 0) ==> d <= array_gcd(arr, n);
  }

  ensures \result == array_gcd(arr, n);
*/
int find_array_gcd(int* arr, int n) {
    /*@
      requires n > 0;
      requires \forall integer i; 0 <= i < n ==> arr[i] >= 0;
    */
    int result = arr[0];

    /*@
      loop invariant 1 <= i <= n;
      loop invariant result >= 0;
      loop invariant result == array_gcd(arr, i);
      // Helper invariant: result divides all elements processed so far
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] % result == 0;
      loop assigns i, result;
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        /*@
          requires result >= 0 && arr[i] >= 0; // Ensure non-negative for calculate_gcd
          // The loop invariant `result == array_gcd(arr, i)` implies that result is positive
          // unless all previous elements were zero. If all elements are zero, result will be 0.
          // If result is 0 and arr[i] is 0, gcd(0,0) is 0.
          // If result is 0 and arr[i] is positive, gcd(0, arr[i]) is arr[i].
          // These are handled by calculate_gcd's postconditions.
        */
        result = calculate_gcd(result, arr[i]);
    }
    return result;
}
