// Task ID: 41
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: For complex logic, define recursive logic functions.
  // This axiomatic block defines a "lambda" function concept for even numbers.
  axiomatic EvenChecker {
    logic int is_even_lambda(int x);

    // Axiom for the lambda function: it returns 1 if x is even, 0 otherwise.
    axiom is_even_lambda_def:
      \forall int x; is_even_lambda(x) == (x % 2 == 0 ? 1 : 0);
  }
*/

/*@
  requires N > 0;
  requires \valid_read(arr + (0..N-1));
  requires \valid_write(filtered_arr + (0..N-1));

  assigns filtered_arr[0..N-1];

  // Rule II.3: Ensures clause for boolean-like function uses <==>.
  // This ensures clause states that the result (number of even elements) is
  // exactly the count of elements in arr for which is_even_lambda returns 1.
  ensures \result == (\num_of(integer i; 0 <= i < N && is_even_lambda(arr[i]) == 1));

  // This ensures clause states that filtered_arr contains only even numbers
  // up to \result, and these are precisely the even numbers from arr in order.
  ensures \forall integer k; 0 <= k < \result ==> is_even_lambda(filtered_arr[k]) == 1;
  ensures \forall integer k; 0 <= k < \result ==>
    \exists integer i; 0 <= i < N && arr[i] == filtered_arr[k] &&
    (\forall integer j; 0 <= j < i && is_even_lambda(arr[j]) == 1 ==> \num_of(integer p; 0 <= p < k && filtered_arr[p] == arr[j]) == 1); // Preserve order
  
  // This ensures clause states that any element in filtered_arr[0..\result-1]
  // must have been an even element from arr.
  ensures \forall integer k; 0 <= k < \result ==> \exists integer i; 0 <= i < N && arr[i] == filtered_arr[k];

  // This ensures clause states that elements beyond \result in filtered_arr are unchanged.
  // This is a common pattern for "filling" an array up to a certain point.
  ensures \forall integer k; \result <= k < N ==> filtered_arr[k] == \old(filtered_arr[k]);
*/
int filter_even_numbers(int arr[], int N, int filtered_arr[]) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= N;
      loop invariant 0 <= count <= i;

      // Rule II.4: Loop invariants.
      // 1. All elements processed so far (arr[0..i-1]) have been checked.
      // 2. filtered_arr[0..count-1] contains only even numbers from arr[0..i-1].
      loop invariant \forall integer k; 0 <= k < count ==> is_even_lambda(filtered_arr[k]) == 1;

      // 3. filtered_arr[0..count-1] contains exactly the even numbers from arr[0..i-1] in order.
      loop invariant \forall integer k; 0 <= k < count ==>
        \exists integer p; 0 <= p < i && arr[p] == filtered_arr[k] && is_even_lambda(arr[p]) == 1 &&
        (\forall integer q; 0 <= q < p && is_even_lambda(arr[q]) == 1 ==> \num_of(integer r; 0 <= r < k && filtered_arr[r] == arr[q]) == 1);

      // 4. count is the number of even elements in arr[0..i-1].
      loop invariant count == (\num_of(integer k; 0 <= k < i && is_even_lambda(arr[k]) == 1));

      // 5. Elements beyond count in filtered_arr up to i are unchanged from their initial state.
      loop invariant \forall integer k; count <= k < i ==> filtered_arr[k] == \at(filtered_arr[k], Pre);

      loop assigns i, count, filtered_arr[0..N-1]; // Specify modified range

      // Rule II.4: Loop variant for termination.
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        // Use the lambda function concept (is_even_lambda)
        if (is_even_lambda(arr[i]) == 1) { // Rule I.2: Check for 1 (true)
            filtered_arr[count] = arr[i];
            count++;
        }
    }
    return count;
}
