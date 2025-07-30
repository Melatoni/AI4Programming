// Task ID: 8
// Generation: 4

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled by Frama-C's understanding of C types.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.5: Prevent Runtime Errors (RTE).
*/

/*@
  // Axiomatic block for the square function, to be used in logic.
  // This helps Frama-C understand the property of squaring a number.
  axiomatic Square {
    logic integer square(integer x) = x * x;

    // Helper axiom: Square of a non-negative number is non-negative.
    axiom square_non_negative:
      \forall integer x; x >= 0 ==> square(x) >= 0;

    // Helper axiom: Square of a number is equal to itself if it's 0 or 1.
    axiom square_zero_one:
      square(0) == 0 && square(1) == 1;

    // Helper axiom: Square of numbers greater than 1 increases quadratically.
    axiom square_increasing_positive:
      \forall integer x, y; x >= 0 && y >= 0 && x <= y ==> square(x) <= square(y);
  }
*/

/*@
  // The function takes an array of integers and its size.
  // It computes the square of each element and stores it back in the same array.
  //
  // @param arr: The array of integers.
  // @param size: The number of elements in the array.
  //
  // Preconditions:
  // - The array pointer must not be NULL.
  // - The size must be non-negative.
  // - Each element in the array, when squared, must not overflow an int.
  //   For a 32-bit signed int, the maximum value is 2,147,483,647.
  //   The square root of this is approximately 46340.
  //   So, elements must be within [-46340, 46340] to avoid overflow on squaring.
  requires \valid(arr + (0..size-1));
  requires size >= 0;
  requires \forall integer i; 0 <= i < size ==> arr[i] >= -46340 && arr[i] <= 46340;

  // Postconditions:
  // - The function assigns to all elements of the array.
  assigns arr[0..size-1];
  // - After execution, each element arr[i] should be the square of its original value.
  ensures \forall integer i; 0 <= i < size ==> arr[i] == \old(square(arr[i]));
*/
void calculate_squares_in_place(int arr[], int size) {
  /*@
    loop invariant 0 <= i <= size;
    loop invariant \forall integer k; 0 <= k < i ==> arr[k] == \old(square(arr[k]));
    loop invariant \forall integer k; i <= k < size ==> arr[k] == \old(arr[k]);
    loop assigns i, arr[0..size-1];
    loop variant size - i;
  */
  for (int i = 0; i < size; i++) {
    // Rule II.5: The precondition `arr[i] >= -46340 && arr[i] <= 46340`
    // prevents `arr[i] * arr[i]` from overflowing.
    arr[i] = arr[i] * arr[i];
  }
}
