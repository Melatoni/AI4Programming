// Task ID: 45
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: int for booleans.
  // Rule I.3: Array pointer decay - not applicable here, as it's a 1D array.

  // Rule II.1, II.2: Recursive logic for GCD.
  // Define an axiomatic block for GCD helper functions.
  axiomatic GCD {
    logic integer gcd(integer a, integer b);

    // Axiom for base cases and recursive step of GCD.
    // Ensure natural numbers for gcd.
    axiom gcd_def:
      \forall integer a, b;
      a > 0 && b > 0 ==> gcd(a, b) == (if b == 0 then a else gcd(b, a % b));

    // Helper axiom: gcd(a,0) = a
    axiom gcd_zero_b:
      \forall integer a;
      a > 0 ==> gcd(a, 0) == a;

    // Helper axiom for symmetry: gcd(a,b) = gcd(b,a)
    axiom gcd_symmetry:
      \forall integer a, b;
      a > 0 && b > 0 ==> gcd(a, b) == gcd(b, a);

    // Helper axiom: gcd(a,a) = a
    axiom gcd_same:
      \forall integer a;
      a > 0 ==> gcd(a, a) == a;

    // Helper axiom: gcd is associative
    axiom gcd_associative:
      \forall integer a, b, c;
      a > 0 && b > 0 && c > 0 ==> gcd(a, gcd(b, c)) == gcd(gcd(a, b), c);

    // Helper axiom: gcd divides both numbers
    axiom gcd_divides_a:
      \forall integer a, b;
      a > 0 && b > 0 ==> a % gcd(a, b) == 0;
    axiom gcd_divides_b:
      \forall integer a, b;
      a > 0 && b > 0 ==> b % gcd(a, b) == 0;

    // Helper axiom: if d divides a and b, then d divides gcd(a,b)
    axiom gcd_greatest_common_divisor:
      \forall integer a, b, d;
      a > 0 && b > 0 && d > 0 && a % d == 0 && b % d == 0 ==> gcd(a, b) % d == 0;

    // Logic function to compute GCD of an array segment.
    // This is crucial for verifying the loop invariant.
    logic integer array_gcd(int* arr, integer from, integer to);

    axiom array_gcd_base:
      \forall int* arr, integer from;
      array_gcd(arr, from, from) == arr[from];

    axiom array_gcd_rec:
      \forall int* arr, integer from, integer to;
      from < to ==> array_gcd(arr, from, to) == gcd(arr[to], array_gcd(arr, from, to - 1));
  }
*/

/*@
  requires N > 0;
  requires \forall integer k; 0 <= k < N ==> arr[k] > 0; // All elements must be positive for GCD definition used.
  assigns \nothing;
  ensures \result == array_gcd(arr, 0, N - 1); // Rule II.3: Use logical equivalence if it were boolean-like. Here, direct equality is fine.
  ensures \forall integer k; 0 <= k < N ==> arr[k] % \result == 0; // The result must divide all elements.
  ensures \forall integer d; d > 0 && (\forall integer k; 0 <= k < N ==> arr[k] % d == 0) ==> \result % d == 0; // The result is the greatest such divisor.
*/
int find_array_gcd(int* arr, int N) {
    int current_gcd = arr[0];

    /*@
      loop invariant 1 <= i <= N;
      loop invariant current_gcd == array_gcd(arr, 0, i - 1);
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] % current_gcd == 0;
      loop invariant \forall integer d; d > 0 && (\forall integer k; 0 <= k < i ==> arr[k] % d == 0) ==> current_gcd % d == 0;
      loop assigns i, current_gcd;
      loop variant N - i; // Rule II.4: Mandatory loop variant.
    */
    for (int i = 1; i < N; i++) {
        // Euclidean algorithm for GCD
        // current_gcd and arr[i] are guaranteed to be positive by loop invariant and requires clause.
        // Rule II.5: Prevention of Runtime Errors (RTE) - Not directly applicable for GCD, as intermediate values don't overflow.
        // The `gcd` function in axiomatic block handles positive inputs.
        // The implementation of gcd itself should prevent infinite loops or division by zero.
        int a = current_gcd;
        int b = arr[i];
        /*@
          loop invariant (a > 0 && b >= 0) || (a == 0 && b > 0); // Both can't be zero, one must be positive.
          loop invariant gcd(\at(current_gcd, LoopEntry), \at(arr[i], LoopEntry)) == gcd(a, b);
          loop assigns a, b;
          loop variant b;
        */
        while (b != 0) {
            int temp = b;
            b = a % b;
            a = temp;
        }
        current_gcd = a;
    }
    return current_gcd;
}
