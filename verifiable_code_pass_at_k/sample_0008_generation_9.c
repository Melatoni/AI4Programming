// Task ID: 8
// Generation: 9

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in formal parameters.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic SquareList {
    logic integer square(integer x) = x * x;

    // Helper axiom for square: if x is in range, x*x is also in range (for non-negative x)
    // Rule II.2: CRITICAL - Helper Axioms
    axiom square_non_negative_range:
      \forall integer x; x >= 0 ==> square(x) >= 0;

    // A property for the maximum possible square value to prevent overflow,
    // assuming input elements are within int range.
    // This axiom helps in reasoning about the upper bound of elements in the output array.
    // For int, max square is INT_MAX if input is sqrt(INT_MAX)
    // We assume int is 32-bit, so INT_MAX is 2,147,483,647.
    // sqrt(INT_MAX) is approx 46340.
    axiom square_max_value:
      \forall integer x; x >= 0 && x <= 46340 ==> square(x) <= 2147483647;
  }
*/

/*@
  requires N >= 0;
  requires \valid_read(list + (0..N-1));
  requires \valid(result + (0..N-1));

  // Rule II.5: Prevent Runtime Errors (RTE) - Overflow check for squaring elements.
  // Assumes 32-bit int. Max positive int for which square doesn't overflow is 46340.
  requires \forall integer i; 0 <= i < N ==> list[i] >= 0 && list[i] <= 46340;

  assigns result[0..N-1];

  // Rule II.3: Ensures clause for boolean-like functions (though this isn't boolean, it dictates the output state).
  ensures \forall integer i; 0 <= i < N ==> result[i] == square(list[i]);
  ensures \fresh{Old, Here}(result); // Ensures result array is entirely written.
*/
void calculate_squares(int* list, int N, int* result) {
    /*@
      loop invariant 0 <= i <= N;
      // Rule II.4: Mandatory Loop Invariant
      loop invariant \forall integer k; 0 <= k < i ==> result[k] == square(list[k]);

      loop assigns i, result[0..N-1];
      // Rule II.4: Mandatory Loop Variant
      loop variant N - i;
    */
    for (int i = 0; i < N; ++i) {
        // Rule II.5: Prevent Runtime Errors (RTE) - ensuring list[i] * list[i] does not overflow.
        // This is primarily handled by the function's requires clause, but good to keep in mind.
        result[i] = list[i] * list[i];
    }
}
