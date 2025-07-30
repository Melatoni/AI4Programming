// Task ID: 8
// Generation: 8

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1, II.2: Recursive logic for complex properties.
  // Define an axiomatic block for the recursive logic function.
  axiomatic SquareListProperties {
    logic integer square_element(integer x);

    axiom square_element_def:
      \forall integer x; square_element(x) == x * x;

    // Rule II.2: Helper axiom to state that squaring a non-negative number
    // results in a non-negative number.
    axiom square_non_negative:
      \forall integer x; x >= 0 ==> square_element(x) >= 0;

    // Helper axiom for the upper bound of the squared value.
    // This axiom depends on the maximum possible value for an int.
    // Assuming 32-bit signed int, INT_MAX is 2^31 - 1.
    // The maximum possible square without overflow for a positive int is (2^15 - 1)^2 ~ 32767^2 ~ 10^9.
    // If x * x is required to fit in int, then x must be <= 46340.
    // The input constraint `requires \forall integer k; 0 <= k < n_in ==> in[k] <= 46340;`
    // ensures that in[k] * in[k] does not overflow int.
    // We can also state that if x * x is in int range, then square_element(x) is x*x.
  }

  // Rule II.5: Prevent Runtime Errors (RTE).
  // Requires:
  // 1. n_in is non-negative.
  // 2. The input array `in` is not null.
  // 3. The output array `out` is not null.
  // 4. The size `n_in` must be consistent with the allocated memory for `in` and `out`.
  //    This is implicitly handled by Frama-C's array bounds checking.
  // 5. CRITICAL: Prevent overflow when squaring elements.
  //    For a 32-bit signed int, INT_MAX is 2^31 - 1 (2147483647).
  //    The largest integer x such that x*x fits in an int is sqrt(INT_MAX) which is 46340.
  requires n_in >= 0;
  requires \valid_read(in + (0..n_in - 1));
  requires \valid(out + (0..n_in - 1));
  requires \forall integer k; 0 <= k < n_in ==> in[k] >= 0; // Assume non-negative inputs for simplicity
  requires \forall integer k; 0 <= k < n_in ==> in[k] <= 46340; // Prevents overflow of in[k]*in[k]

  // Assigns: Modifies the `out` array.
  assigns out[0..n_in - 1];

  // Ensures:
  // After execution, each element in `out` should be the square of the corresponding element in `in`.
  ensures \forall integer k; 0 <= k < n_in ==> out[k] == square_element(in[k]);
  ensures \fresh(out); // Ensures out is modified, not just its content.
*/
void square_list(int *in, int *out, int n_in) {
    /*@
      loop invariant 0 <= i <= n_in;
      loop invariant \forall integer k; 0 <= k < i ==> out[k] == square_element(in[k]);
      loop assigns i, out[0..n_in - 1]; // Rule II.4: Mandatory loop assigns.
      loop variant n_in - i; // Rule II.4: Mandatory loop variant.
    */
    for (int i = 0; i < n_in; i++) {
        // Rule II.5: The `requires` clause ensures `in[i] * in[i]` does not overflow.
        out[i] = in[i] * in[i];
    }
}
