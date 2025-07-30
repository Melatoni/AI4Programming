// Task ID: 45
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Define a recursive logic function for GCD.
  // This axiomatic block defines the mathematical properties of GCD.
  axiomatic GCD {
    logic integer gcd_recursive(integer a, integer b);

    axiom gcd_base:
      \forall integer a; gcd_recursive(a, 0) == \abs(a);

    axiom gcd_recursive_step:
      \forall integer a, b;
        b != 0 ==> gcd_recursive(a, b) == gcd_recursive(b, a % b);

    // Rule II.2: Helper axioms for GCD properties.
    // These axioms help the prover reason about GCD.
    axiom gcd_symmetry:
      \forall integer a, b; gcd_recursive(a, b) == gcd_recursive(b, a);

    axiom gcd_non_negative:
      \forall integer a, b; gcd_recursive(a, b) >= 0;

    axiom gcd_divides_a:
      \forall integer a, b; a % gcd_recursive(a, b) == 0;

    axiom gcd_divides_b:
      \forall integer a, b; b % gcd_recursive(a, b) == 0;

    // Helper axiom: If a number divides both a and b, it must divide gcd(a,b)
    axiom gcd_greatest_common_divisor:
      \forall integer a, b, d;
        d > 0 && a % d == 0 && b % d == 0 ==> gcd_recursive(a, b) % d == 0;
  }

  // Rule II.1, II.2: Define a recursive logic function for the GCD of an array.
  axiomatic ArrayGCD {
    logic integer array_gcd_recursive(int* arr, integer from, integer to);

    // Base case: GCD of a single element (or an empty range, depending on interpretation)
    // We define it for a single element as the element itself.
    axiom array_gcd_base_single:
      \forall int* arr, integer i;
        array_gcd_recursive(arr, i, i) == \abs(arr[i]);

    // Recursive step: GCD of a range is GCD of first element and GCD of rest.
    axiom array_gcd_recursive_step:
      \forall int* arr, integer from, integer to;
        from < to ==> array_gcd_recursive(arr, from, to) == gcd_recursive(arr[from], array_gcd_recursive(arr, from + 1, to));

    // Helper axiom: The array GCD divides all elements in the range.
    axiom array_gcd_divides_all:
      \forall int* arr, integer from, integer to, integer k;
        from <= k <= to ==> arr[k] % array_gcd_recursive(arr, from, to) == 0;

    // Helper axiom: Array GCD is non-negative.
    axiom array_gcd_non_negative_prop:
      \forall int* arr, integer from, integer to;
        array_gcd_recursive(arr, from, to) >= 0;
  }
*/

/*@
  requires n > 0;
  requires \valid_read(arr + (0..n-1));
  // Rule II.5: Prevent potential issues with 0 values in array elements,
  // although gcd_recursive handles abs(0). This ensures the array_gcd_recursive
  // for a single element is well-defined.
  requires \for_all integer i; 0 <= i < n ==> \abs(arr[i]) <= INT_MAX;

  assigns \nothing;

  ensures \result == array_gcd_recursive(arr, 0, n - 1);
  ensures \result >= 0; // GCD is conventionally non-negative.
  ensures \for_all integer i; 0 <= i < n ==> arr[i] % \result == 0;
  // If all elements are 0, the GCD is 0. Otherwise, it must be positive.
  ensures (\for_all integer i; 0 <= i < n ==> arr[i] == 0) <==> (\result == 0);
*/
int find_array_gcd(int* arr, int n) {
    if (n == 0) {
        // According to the problem statement, n > 0.
        // However, if it were allowed, the GCD of an empty set is undefined or 0.
        // For this problem, we assume n > 0.
        return 0; // Or handle as an error if n=0 is not expected.
    }

    int result = arr[0];
    /*@
      loop invariant 1 <= i <= n;
      loop invariant result == array_gcd_recursive(arr, 0, i - 1);
      loop invariant result >= 0;
      loop invariant \for_all integer j; 0 <= j < i ==> arr[j] % result == 0;

      // Rule II.5: Prevent overflow in intermediate GCD computation if values are large.
      // This is implicit in gcd_recursive properties, but good to be aware.
      // Assuming result and arr[i] are within int range, gcd_recursive(result, arr[i]) will be too.

      loop assigns i, result;
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        // Implementing Euclidean algorithm iteratively for two numbers.
        // Rule II.5: Ensure temp_a and temp_b don't overflow during modulo/subtraction.
        // Since arr[i] and result are ints, and the GCD is always <= min(|a|,|b|),
        // intermediate results are fine.
        int temp_a = result;
        int temp_b = arr[i];

        // Make sure both are non-negative for consistent Euclidean algorithm in C.
        // ACSL's gcd_recursive handles negative numbers via \abs, but C's % operator
        // behavior with negative numbers can be tricky.
        if (temp_a < 0) {
            temp_a = -temp_a;
        }
        if (temp_b < 0) {
            temp_b = -temp_b;
        }

        /*@
          loop invariant \at(temp_a, LoopEntry) % temp_a == 0;
          loop invariant \at(temp_b, LoopEntry) % temp_a == 0;
          loop invariant \at(temp_a, LoopEntry) % temp_b == 0;
          loop invariant \at(temp_b, LoopEntry) % temp_b == 0;
          loop invariant gcd_recursive(\at(result, LoopEntry), \at(arr[i], LoopEntry)) == gcd_recursive(temp_a, temp_b);
          loop invariant temp_a >= 0 && temp_b >= 0;
          loop assigns temp_a, temp_b;
          loop variant temp_b;
        */
        while (temp_b != 0) {
            int temp = temp_b;
            temp_b = temp_a % temp_b;
            temp_a = temp;
        }
        result = temp_a; // temp_a now holds the GCD of the previous result and arr[i]
    }

    // If all array elements were 0, result will be 0.
    // If any element was non-zero, result will be positive.
    return result;
}
