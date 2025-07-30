// Task ID: 8
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: Ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Axiomatic block for proving properties about squares
  axiomatic SquareProperties {
    logic integer square(integer x);

    axiom square_def:
      \forall integer x; square(x) == x * x;

    // Helper axiom: Square of a non-negative number is non-negative
    axiom square_non_negative:
      \forall integer x; x >= 0 ==> square(x) >= 0;

    // Helper axiom: Square of a number within a range (for overflow prevention)
    // If x is in [min, max], then x*x is in [0, max*max] (assuming min >= 0)
    // For int, max is INT_MAX, so we need to ensure x <= sqrt(INT_MAX)
    // INT_MAX is 2147483647, sqrt(INT_MAX) approx 46340.95
    axiom square_max_val:
      \forall integer x; x >= 0 && x <= 46340 ==> square(x) <= 2147483647;
  }
*/

/*@
  requires N >= 0;
  // Rule II.5: Prevent overflow for individual elements' squares.
  // Assuming elements are non-negative, as negative squares could exceed INT_MAX.
  // If negative numbers are allowed, a more complex requires involving MIN_INT and MAX_INT is needed.
  // For simplicity, we assume non-negative inputs for the elements to prevent overflow.
  // For each element arr[i], it must be <= 46340 to prevent arr[i]*arr[i] overflow.
  requires \forall integer i; 0 <= i < N ==> arr[i] >= 0 && arr[i] <= 46340;

  // Rule I.3: Array pointer decay - arr is int*, not int[].
  // Rule II.5: Ensure the output array `res` is large enough.
  requires \valid_range(arr, 0, N-1);
  requires \valid_range(res, 0, N-1);

  assigns res[0..N-1];

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The function computes squares, so each element in res should be the square of the corresponding element in arr.
  ensures \forall integer i; 0 <= i < N ==> res[i] == square(arr[i]);
  ensures \result == 0; // The function doesn't return a boolean, so a simple return value is fine.
*/
void compute_squares(int arr[], int N, int res[]) {
  /*@
    loop invariant 0 <= i <= N;
    loop invariant \forall integer k; 0 <= k < i ==> res[k] == square(arr[k]);
    loop assigns i, res[0..N-1];
    loop variant N - i;
  */
  for (int i = 0; i < N; i++) {
    // Rule II.5: The `requires` clause already ensures arr[i]*arr[i] does not overflow.
    res[i] = arr[i] * arr[i];
  }
}
