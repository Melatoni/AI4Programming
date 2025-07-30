// Task ID: 41
// Generation: 8

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled if applicable.
*/

/*@
  // Rule II.1: No \sum.
  // Rule II.2: Helper axioms for recursive logic not strictly needed for this problem.
  // Rule II.5: Prevent Runtime Errors.
  requires \valid_read(arr + (0..size-1));
  requires size >= 0;
  // Constraint to prevent potential overflow in computations if intermediate results were stored,
  // though for this specific problem, it's less critical for simple assignments.
  // It's good practice to consider potential range issues.
  requires \forall integer k; 0 <= k < size ==> arr[k] >= -2147483648 && arr[k] <= 2147483647;

  assigns \nothing; // This function only checks, doesn't modify.

  // Rule II.3: Ensures clause for boolean-like function uses <==>.
  // The function returns 1 if all elements are even, 0 otherwise.
  ensures (\forall integer k; 0 <= k < size ==> arr[k] % 2 == 0) <==> (\result == 1);
*/
int all_even(int* arr, int size) {
    /*@
      loop invariant 0 <= i <= size;
      // Rule II.4: Loop invariant capturing the state.
      // All elements checked so far (from 0 to i-1) are even.
      loop invariant \forall integer k; 0 <= k < i ==> arr[k] % 2 == 0;
      loop assigns i;
      // Rule II.4: Loop variant for termination.
      loop variant size - i;
    */
    for (int i = 0; i < size; ++i) {
        // Rule III.1: No C-style ternary in ACSL.
        // Rule III.2: No parentheses around if-then-else.
        // Rule III.3: Correct range syntax.
        // Rule III.4: No stray semicolons.
        if (arr[i] % 2 != 0) {
            return 0; // Found an odd number, so not all are even.
        }
    }
    return 1; // All numbers were even.
}
