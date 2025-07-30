// Task ID: 8
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as we pass array size.
*/

/*@
  // Rule II.1: Recursive logic for complexity - not needed for this problem.
  // Rule II.2: Helper axioms - not needed for this problem.
  // Rule II.3: ensures clause for boolean-like functions - not applicable as no boolean return.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
*/

/*@
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  requires N >= 0;
  requires \valid_read(list + (0..N-1));
  requires \valid_write(result + (0..N-1));
  // Rule II.5: Prevent Runtime Errors (RTE) - check for potential overflow during squaring.
  // Assuming int is 32-bit, max value is 2,147,483,647. Sqrt(2,147,483,647) is approx 46340.
  // So, individual elements in list must not exceed 46340 to prevent overflow when squared.
  requires \forall integer k; 0 <= k < N ==> -46340 <= list[k] <= 46340;

  assigns result[0..N-1];

  ensures \forall integer k; 0 <= k < N ==> result[k] == list[k] * list[k];
  ensures \fresh(result); // result points to newly written memory
*/
void square_list(int list[], int N, int result[]) {
    /*@
      loop invariant 0 <= i <= N;
      loop invariant \forall integer k; 0 <= k < i ==> result[k] == list[k] * list[k];
      loop assigns i, result[0..N-1];
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        result[i] = list[i] * list[i];
    }
}
