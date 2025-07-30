// Task ID: 45
// Generation: 2

/*@
  // Axiomatic definition for GCD:
  // Rule II.1: Recursive logic for complex properties.
  axiomatic GCD {
    logic integer gcd(integer a, integer b);

    axiom gcd_base_a:
      \forall integer b; gcd(0, b) == (\abs(b));

    axiom gcd_base_b:
      \forall integer a; gcd(a, 0) == (\abs(a));

    axiom gcd_recursive:
      \forall integer a, b;
        a != 0 && b != 0 ==> gcd(a, b) == gcd(b, a % b);

    // Helper axioms (Rule II.2) to establish properties for the prover.
    // These are crucial for proving loop invariants and postconditions.
    axiom gcd_positive:
      \forall integer a, b; gcd(a, b) >= 0;

    axiom gcd_divides_a:
      \forall integer a, b; a % gcd(a, b) == 0;

    axiom gcd_divides_b:
      \forall integer a, b; b % gcd(a, b) == 0;

    axiom gcd_greatest:
      \forall integer a, b, d;
        a % d == 0 && b % d == 0 ==> d <= gcd(a, b);
  }

  // Axiomatic definition for GCD of an array:
  axiomatic ArrayGCD {
    logic integer array_gcd(int* arr, integer from, integer to);

    axiom array_gcd_single_element:
      \forall int* arr, integer i;
        array_gcd(arr, i, i) == \abs(arr[i]);

    axiom array_gcd_two_elements:
      \forall int* arr, integer i, j;
        i < j ==> array_gcd(arr, i, j) == gcd(arr[i], array_gcd(arr, i + 1, j));

    // Helper axiom: If all elements are zero, array_gcd is zero.
    // This is useful when all elements are 0, where gcd(0,0)=0.
    axiom array_gcd_all_zeros:
      \forall int* arr, integer from, integer to;
        from <= to && (\forall integer k; from <= k <= to ==> arr[k] == 0) ==> array_gcd(arr, from, to) == 0;
  }
*/

/*@
  requires n > 0;
  // Rule II.5: Prevent potential issues if all elements are 0, ensuring gcd is 0.
  // This is implicitly handled by the axiomatic definition, but good to note.
  // For non-zero elements, the result will be positive.
  // Ensures the array elements are within a range where their GCD doesn't overflow int.
  // Though typically GCD is smaller than its inputs, it's good practice.
  requires \forall integer k; 0 <= k < n ==> arr[k] >= -2147483648 && arr[k] <= 2147483647;

  assigns \nothing;

  // Rule II.3: Ensures the result matches the logical definition.
  ensures \result == array_gcd(arr, 0, n - 1);
*/
int find_array_gcd(int* arr, int n) {
    // Handle the case of a single element array.
    // Although the loop handles n=1, this is more direct for the base case.
    if (n == 1) {
        return arr[0] < 0 ? -arr[0] : arr[0]; // \abs(arr[0])
    }

    int result = arr[0];

    /*@
      loop invariant 1 <= i <= n;
      // The result variable holds the GCD of elements from arr[0] to arr[i-1].
      loop invariant result == array_gcd(arr, 0, i - 1);
      // Ensures that 'result' is always non-negative, as GCD is defined to be.
      loop invariant result >= 0;
      // Each element processed so far is divisible by the current 'result'.
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] % result == 0;

      loop assigns i, result;
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        // Euclidean Algorithm to find GCD of two numbers.
        // It's crucial that this inner loop's properties are implicitly proven
        // by the axiomatic definition of gcd.
        int a = result;
        int b = arr[i];

        /*@
          loop invariant gcd(a, b) == gcd(\old(a), \old(b));
          loop invariant a >= 0 || b >= 0; // At least one non-negative for termination
          loop assigns a, b;
          loop variant \abs(b); // Termination variant for Euclidean algorithm
        */
        while (b != 0) {
            int temp = b;
            b = a % b;
            a = temp;
        }
        // After the inner loop, 'a' holds gcd(\old(result), arr[i]).
        result = a;
    }

    return result;
}
