// Task ID: 21
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled by ACSL.

  // Rule II.1: Recursive logic for complexity (not needed here, but good to remember).
  // Rule II.2: Helper axioms (not needed here).
  // Rule II.3: ensures clause for boolean-like functions (not applicable here as it returns an array).
  // Rule II.5: Prevent Runtime Errors (RTE).

  requires m >= 0;
  requires n >= 0;

  // The maximum possible value for a multiple is m * n.
  // We need to ensure that m * n does not overflow an int.
  // Assuming int is 32-bit, INT_MAX is 2,147,483,647.
  // A safe upper bound for m and n to prevent overflow:
  // If m = 1, n <= INT_MAX.
  // If m = INT_MAX, n <= 1.
  // A more general safe bound: sqrt(INT_MAX) is approx 46340.
  // So, if both m and n are <= 46340, m * n will not overflow.
  // This is a pragmatic choice to cover common cases without making the requires too restrictive.
  requires m <= 46340;
  requires n <= 46340;

  // Ensure the output array 'multiples' is large enough to hold 'm' elements.
  // This is typically done by the caller, but we can assume it for the function's contract.
  // The client code should allocate an array of size 'm'.
  requires \valid(multiples + (0..m-1));

  // The function modifies the content of the 'multiples' array.
  assigns multiples[0..m-1];

  // Post-condition:
  // After execution, for each index i from 0 to m-1,
  // the element multiples[i] should be equal to (i+1) * n.
  ensures \forall integer i; 0 <= i < m ==> multiples[i] == (i + 1) * n;
*/
void find_multiples(int m, int n, int multiples[]) {
    /*@
      loop invariant 0 <= i <= m;
      loop invariant \forall integer k; 0 <= k < i ==> multiples[k] == (k + 1) * n;
      loop assigns i, multiples[0..m-1];
      loop variant m - i;
    */
    for (int i = 0; i < m; i++) {
        // Rule II.5: Prevent runtime errors.
        // The loop invariant `multiples[k] == (k+1)*n` for k < i
        // and loop variant `m-i` ensure that `i+1` will not exceed `m`.
        // The `requires m <= 46340 && n <= 46340` ensures that `(i+1)*n` will not overflow.
        multiples[i] = (i + 1) * n;
    }
}
