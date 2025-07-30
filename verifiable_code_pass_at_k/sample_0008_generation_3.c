// Task ID: 8
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as it's a simple array.
  // Rule II.1: Recursive logic for complexity - not applicable here.
  // Rule II.2: Helper axioms - not applicable here.
  // Rule II.3: ensures clause for boolean-like functions - not applicable here.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  requires n > 0;
  requires \valid_read(arr + (0..n-1));
  requires \valid_write(result_arr + (0..n-1));

  // Rule II.5: Prevent Runtime Errors (RTE) - ensure no overflow for squaring elements.
  // For signed int, sqrt(INT_MAX) is approx 46340.
  // This ensures that arr[i] * arr[i] does not overflow.
  requires \forall integer i; 0 <= i < n ==> arr[i] >= -46340 && arr[i] <= 46340;

  assigns result_arr[0..n-1];

  // The ensures clause states that each element in result_arr is the square of the corresponding element in arr.
  ensures \forall integer i; 0 <= i < n ==> result_arr[i] == arr[i] * arr[i];
  ensures \result == result_arr; // Return the modified array pointer.
*/
int* apply_square_lambda(int* arr, int n, int* result_arr) {
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> result_arr[k] == arr[k] * arr[k];
      loop assigns i, result_arr[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // Rule II.5: The `requires` clause already ensures `arr[i] * arr[i]` doesn't overflow.
        result_arr[i] = arr[i] * arr[i];
    }
    return result_arr;
}
