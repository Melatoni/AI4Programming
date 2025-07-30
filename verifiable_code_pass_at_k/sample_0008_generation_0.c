// Task ID: 8
// Generation: 0

/*@ axiomatic Squares {
  @   logic integer square(integer x);
  @   axiom square_def:
  @     \forall integer x; square(x) == x * x;
  @
  @   // Rule II.2: Helper axiom for proving properties of squares.
  @   // If x is within a certain range, its square is also within a derived range.
  @   axiom square_non_negative:
  @     \forall integer x; square(x) >= 0;
  @
  @   // Helper axiom to bound the square if the input is bounded.
  @   // This helps in proving that the result array elements are within int range.
  @   axiom square_bound:
  @     \forall integer x, integer M;
  @       (x >= -M && x <= M) ==> (square(x) >= 0 && square(x) <= M * M);
  @ }
  @*/

/*@
  @ requires n >= 0;
  @ requires \valid_read(arr + (0..n-1));
  @ requires \valid(result + (0..n-1));
  @
  @ // Rule II.5: Prevent overflow for square(arr[i]).
  @ // For 32-bit int, the maximum value is 2,147,483,647.
  @ // sqrt(2,147,483,647) is approx 46340.95. So, if elements are within [-46340, 46340],
  @ // their squares will not overflow.
  @ requires \forall integer i; 0 <= i < n ==> arr[i] >= -46340 && arr[i] <= 46340;
  @
  @ assigns result[0..n-1];
  @
  @ ensures \forall integer i; 0 <= i < n ==> result[i] == square(arr[i]);
  @ ensures \fresh(result); // Indicates that result array memory is newly written
  @*/
void lambda_squares(int arr[], int n, int result[]) {
    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall integer k; 0 <= k < i ==> result[k] == square(arr[k]);
      @ loop assigns i, result[0..n-1];
      @ loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        result[i] = arr[i] * arr[i]; // This is the "lambda function" application
    }
}
