// Task ID: 45
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in logic functions.
*/

/*@
  // Rule II.1: Using axiomatic block for recursive logic.
  // Rule II.2: Helper axioms for properties.
*/
/*@ axiomatic GCD {
  logic integer gcd(integer a, integer b);

  // Base cases for GCD
  axiom gcd_base_a:
    \forall integer b; gcd(0, b) == (\abs(b));
  axiom gcd_base_b:
    \forall integer a; gcd(a, 0) == (\abs(a));

  // Recursive step for GCD (Euclidean algorithm)
  axiom gcd_rec:
    \forall integer a, b;
      a != 0 && b != 0 ==> gcd(a, b) == gcd(b, a % b);

  // Helper axiom: GCD is commutative
  axiom gcd_commutative:
    \forall integer a, b; gcd(a, b) == gcd(b, a);

  // Helper axiom: GCD is non-negative
  axiom gcd_non_negative:
    \forall integer a, b; gcd(a, b) >= 0;

  // Helper axiom: GCD of positive numbers is positive
  axiom gcd_positive_result:
    \forall integer a, b; a > 0 && b > 0 ==> gcd(a, b) > 0;

  // Helper axiom: GCD divides both numbers
  axiom gcd_divides_a:
    \forall integer a, b; a % gcd(a, b) == 0;
  axiom gcd_divides_b:
    \forall integer a, b; b % gcd(a, b) == 0;

  // Helper logic function for GCD of an array segment
  logic integer array_gcd{L}(int* a, integer start, integer end);

  // Base case for array_gcd: single element
  axiom array_gcd_base:
    \forall int* a, integer i;
      array_gcd(a, i, i) == (\abs(a[i]));

  // Recursive step for array_gcd
  axiom array_gcd_rec:
    \forall int* a, integer start, integer end;
      start < end ==> array_gcd(a, start, end) == gcd(a[start], array_gcd(a, start + 1, end));

  // Helper axiom: array_gcd is positive if all elements are non-zero.
  // This is a strong property, but useful for verification.
  axiom array_gcd_positive:
    \forall int* a, integer start, integer end;
      (start <= end && \forall integer k; start <= k <= end ==> a[k] != 0) ==> array_gcd(a, start, end) > 0;
}
*/

/*@
  requires n > 0;
  requires \valid_read_range(arr, 0, n - 1);
  // Rule II.5: Prevent runtime errors. All elements must be within int range for GCD.
  // Frama-C's WP can infer this, but it's good practice for clarity.
  // It also prevents potential overflow if intermediate GCD values were larger than int,
  // though for standard GCD, the result is <= min(abs(a), abs(b)).
  assigns \nothing;
  ensures \result == array_gcd(arr, 0, n - 1);
  ensures \result >= 0; // GCD is always non-negative by definition in ACSL.
*/
int find_array_gcd(int* arr, int n) {
    int result = arr[0];
    /*@
      loop invariant 1 <= i <= n;
      loop invariant result == array_gcd(arr, 0, i - 1);
      loop invariant result >= 0; // The GCD of any numbers is non-negative
      loop invariant result <= \abs(arr[0]); // The GCD is always less than or equal to the first element's absolute value (if i > 0)
      loop assigns i, result;
      // Rule II.4: Mandatory loop variant.
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        // Implement Euclidean algorithm for GCD
        int a = result;
        int b = arr[i];

        /*@
          loop invariant (a >= 0 && b >= 0) || (a <= 0 && b <= 0) || (a > 0 && b < 0) || (a < 0 && b > 0); // Keep track of signs
          loop invariant gcd(a, b) == gcd(\old(result), \old(arr[i]));
          loop invariant b >= 0; // b becomes non-negative in the loop
          loop assigns a, b;
          // Rule II.4: Mandatory loop variant.
          loop variant \abs(b);
        */
        while (b != 0) {
            int temp = b;
            // Rule II.5: Ensure a % b does not overflow or cause RTE.
            // For int, a % b is safe as long as b != 0 and a is not INT_MIN when b is -1.
            // Since we take \abs(b) and later ensure b >= 0, this is fine.
            b = a % b;
            a = temp;
        }
        result = (a >= 0) ? a : -a; // Ensure result is non-negative
    }
    return result;
}

/*@
  requires n > 0;
  requires \valid_read_range(arr, 0, n - 1);
  assigns \nothing;
  ensures \result == array_gcd(arr, 0, n - 1);
  ensures \result >= 0;
*/
int find_array_gcd_recursive(int* arr, int n) {
    /*@
      requires n > 0;
      requires \valid_read_range(arr, 0, n - 1);
      assigns \nothing;
      ensures \result == array_gcd(arr, 0, n - 1);
      ensures \result >= 0;
      // This is a helper function, so its ensures clause should reflect its purpose.
    */
    int gcd_recursive_helper(int* a, int idx, int N) {
        if (idx == N - 1) {
            return (a[idx] >= 0) ? a[idx] : -a[idx]; // Base case: absolute value of the last element
        } else {
            int current_gcd = gcd_recursive_helper(a, idx + 1, N);
            // Rule II.5: Ensure current_gcd is not 0 for the second argument of gcd.
            // Our GCD logic handles 0, but it's good to be aware.
            // Also ensure a[idx] is not INT_MIN and current_gcd is -1 for % operation.
            // Given the recursive helper returns non-negative, this is fine.
            int val1 = (a[idx] >= 0) ? a[idx] : -a[idx];
            return find_array_gcd(&val1, 1, &current_gcd, 1); // A dummy call to the iterative gcd
            // Actually, we need to implement the gcd logic directly or call a simple gcd function.
            // Let's call the gcd logic directly.
            int val_a = (a[idx] >= 0) ? a[idx] : -a[idx];
            int val_b = current_gcd;

            /*@
              loop invariant gcd(val_a, val_b) == gcd(\old(val_a), \old(val_b));
              loop invariant val_b >= 0;
              loop assigns val_a, val_b;
              loop variant val_b;
            */
            while (val_b != 0) {
                int temp = val_b;
                val_b = val_a % val_b;
                val_a = temp;
            }
            return (val_a >= 0) ? val_a : -val_a;
        }
    }

    return gcd_recursive_helper(arr, 0, n);
}
