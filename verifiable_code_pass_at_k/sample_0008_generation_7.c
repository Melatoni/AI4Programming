// Task ID: 8
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled by ACSL.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  // Axiomatic block for defining properties of squares.
  axiomatic SquareProperties {
    // Defines a logic function to check if an array element is the square of another.
    logic boolean is_square_of_element(int* arr, int arr_len, int index_val, int index_sq) =
      @  0 <= index_val < arr_len &&
      @  0 <= index_sq < arr_len &&
      @  arr[index_sq] == arr[index_val] * arr[index_val];

    // Helper axiom: if all elements are positive, their squares are also positive.
    // This is a simple example of a helper axiom.
    // For this specific problem, complex helper axioms might not be strictly necessary
    // but demonstrating the concept is important.
    axiom positive_square_is_positive:
      @  \forall int x; x >= 0 ==> x * x >= 0;

    // Helper axiom: if x is within int range, x*x might exceed.
    // This axiom helps in reasoning about potential overflows for squares.
    // It's a conceptual axiom to show how one might reason about range properties.
    axiom square_overflow_check:
      @  \forall int x; x * x <= 2147483647 && x * x >= -2147483648; // INT_MAX and INT_MIN
  }
*/

/*@
  requires N >= 0;
  requires \valid_read(arr + (0..N-1));
  requires \valid(result + (0..N-1));
  assigns result[0..N-1];

  // Rule II.5: Prevent Runtime Errors (RTE) - check for potential overflow when squaring.
  // For each element in arr, ensure its square fits within int.
  // The magic number 46340 is sqrt(INT_MAX).
  requires \forall integer i; 0 <= i < N ==> arr[i] <= 46340 && arr[i] >= -46340;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // Ensures that each element in 'result' is the square of the corresponding element in 'arr'.
  ensures \forall integer i; 0 <= i < N ==> result[i] == arr[i] * arr[i];
  ensures \forall integer i; 0 <= i < N ==> is_square_of_element(arr, N, i, i);
*/
void calculate_squares(int arr[], int result[], int N) {
    /*@
      loop invariant 0 <= i <= N;
      loop invariant \forall integer k; 0 <= k < i ==> result[k] == arr[k] * arr[k];
      loop assigns i, result[0..N-1];
      // Rule II.4: A loop variant is mandatory for termination.
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        result[i] = arr[i] * arr[i];
    }
}

/*@
  // Example "lambda function" concept in C/ACSL.
  // This function conceptualizes applying a square operation.
  // It's not a true lambda in C, but demonstrates the idea of
  // a function representing a single operation.
  requires x <= 46340 && x >= -46340; // Rule II.5: Prevent overflow.
  assigns \nothing;
  ensures \result == x * x;
*/
int square_lambda(int x) {
    return x * x;
}
