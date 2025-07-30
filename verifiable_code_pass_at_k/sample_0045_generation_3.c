// Task ID: 45
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Recursive logic for GCD.
  // Helper axioms for properties of GCD (e.g., commutativity, associativity, etc.)
  // These are often needed for WP to prove properties about recursive functions.
  axiomatic GCD {
    logic integer gcd(integer a, integer b);

    axiom gcd_base_a:
      \forall integer a; a > 0 ==> gcd(a, 0) == a;

    axiom gcd_base_b:
      \forall integer b; b > 0 ==> gcd(0, b) == b;

    axiom gcd_recursive:
      \forall integer a, b;
        a > 0 && b > 0 ==> gcd(a, b) == gcd(b, a % b);

    // Helper axioms (lemmas) for common GCD properties
    // These are crucial for the prover to reason about the function's behavior.
    axiom gcd_commutative:
      \forall integer a, b; gcd(a, b) == gcd(b, a);

    axiom gcd_non_negative:
      \forall integer a, b; a >= 0 && b >= 0 ==> gcd(a, b) >= 0;

    axiom gcd_divides_a:
      \forall integer a, b; a >= 0 && b >= 0 ==> a % gcd(a, b) == 0;

    axiom gcd_divides_b:
      \forall integer a, b; a >= 0 && b >= 0 ==> b % gcd(a, b) == 0;

    axiom gcd_greatest:
      \forall integer a, b, d;
        a >= 0 && b >= 0 && d > 0 && a % d == 0 && b % d == 0 ==> d <= gcd(a, b);
  }

  // Rule II.1, II.2: Recursive logic for GCD of an array.
  axiomatic ArrayGCD {
    logic integer array_gcd(int* arr, integer n);

    axiom array_gcd_base:
      \forall int* arr; array_gcd(arr, 1) == arr[0];

    axiom array_gcd_recursive:
      \forall int* arr, integer n;
        n > 1 ==> array_gcd(arr, n) == gcd(arr[n-1], array_gcd(arr, n-1));

    // Helper axiom: array_gcd is positive if all elements are positive
    axiom array_gcd_positive:
      \forall int* arr, integer n;
        n > 0 && (\forall integer i; 0 <= i < n ==> arr[i] > 0) ==> array_gcd(arr, n) > 0;
  }
*/

/*@
  requires n > 0;
  requires \valid_read_range(arr, 0, n - 1);
  // Rule II.5: Prevent runtime errors. All array elements must be non-negative.
  // GCD is typically defined for non-negative integers.
  requires \forall integer i; 0 <= i < n ==> arr[i] >= 0;
  // If all elements are 0, GCD is 0. If some are > 0, GCD must be > 0.
  // To avoid division by zero internally if an element is 0 and others are not,
  // we assume at least one element is positive if n > 1.
  // A common convention is gcd(0,0)=0. gcd(x,0)=x.
  // To make the proofs easier, we require at least one element to be positive
  // unless n=1 and arr[0]=0.
  requires n == 1 || (\exists integer i; 0 <= i < n && arr[i] > 0);

  assigns \nothing;

  // Rule II.3: Ensures clause uses logical equivalence.
  ensures \result == array_gcd(arr, n);
*/
int find_array_gcd(int* arr, int n) { // Rule I.3: Array parameter decay.
    int result;

    /*@
      loop invariant 0 <= i && i <= n;
      loop invariant i == 1 ==> result == arr[0];
      loop invariant i > 1 ==> result == array_gcd(arr, i);
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] >= 0;
      loop assigns i, result;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (i == 0) {
            result = arr[0];
        } else {
            // Rule II.5: Prevent runtime errors (e.g., division by zero in gcd logic if result becomes 0 unexpectedly)
            // The axiomatic definition handles gcd(x,0) and gcd(0,y).
            // We need to ensure arr[i] is non-negative, which is covered by the function's precondition.
            // result is also non-negative due to loop invariant and initial value.
            int a = result;
            int b = arr[i];

            // Compute gcd(a, b) using Euclidean algorithm
            /*@
              loop invariant \forall integer k;
                (k >= 0 && k < i ==> arr[k] >= 0) &&
                arr[i] >= 0; // Check current element is non-negative
              loop invariant gcd(a,b) == gcd(\at(result,LoopEntry), \at(arr[i],LoopEntry));
              loop invariant a >= 0 && b >= 0;
              loop assigns a, b;
              loop variant a + b; // Or a if b is always smaller, or max(a,b)
            */
            while (b != 0) {
                int temp = b;
                b = a % b;
                a = temp;
            }
            result = a;
        }
    }
    return result;
}
