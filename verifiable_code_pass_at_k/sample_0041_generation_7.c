// Task ID: 41
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic EvenFilter {
    logic int is_even_logic(int x) = (x % 2 == 0);

    // Rule II.1: Recursive logic for properties over sequences.
    // This logic function checks if all elements up to `upper` in the array satisfy the `is_even_logic` predicate.
    logic int all_even_up_to(int* arr, int upper);

    axiom all_even_up_to_base:
      \forall int* arr;
      all_even_up_to(arr, -1) == 1; // Base case: an empty prefix is considered all even.

    axiom all_even_up_to_recursive:
      \forall int* arr, integer k;
      k >= 0 ==>
      all_even_up_to(arr, k) == (is_even_logic(arr[k]) && all_even_up_to(arr, k - 1));

    // Rule II.2: Helper axioms for properties of recursive functions.
    // If all elements up to `n-1` are even, then `all_even_up_to(arr, n-1)` is 1.
    axiom all_even_up_to_implies_true:
      \forall int* arr, integer n;
      n >= 0 && (\forall integer j; 0 <= j < n ==> is_even_logic(arr[j])) ==> all_even_up_to(arr, n - 1) == 1;

    // If `all_even_up_to(arr, n-1)` is 1, then all elements up to `n-1` are even.
    axiom all_even_up_to_implies_property:
      \forall int* arr, integer n;
      n >= 0 && all_even_up_to(arr, n - 1) == 1 ==> (\forall integer j; 0 <= j < n ==> is_even_logic(arr[j]));

    // If `all_even_up_to(arr, n-1)` is 0, then there exists at least one odd element.
    axiom all_even_up_to_implies_false:
      \forall int* arr, integer n;
      n >= 0 && all_even_up_to(arr, n - 1) == 0 ==> (\exists integer j; 0 <= j < n && !is_even_logic(arr[j]));
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent RTE - ensure array access is within bounds.
  requires \valid_read_range(arr, 0, n - 1);
  requires \valid_write_range(result_arr, 0, n - 1);

  assigns result_arr[0..n-1];

  // Rule II.3: Ensures clause uses logical equivalence.
  // The function returns the count of even numbers.
  ensures \result >= 0 && \result <= n;
  ensures \forall integer k; 0 <= k < \result ==> is_even_logic(result_arr[k]);
  ensures \forall integer k; \result <= k < n ==> !is_even_logic(result_arr[k]); // This part effectively states that
                                                                                // beyond `\result`, elements are not even (or undefined).
                                                                                // A more precise postcondition would be that
                                                                                // `result_arr` contains exactly the even elements
                                                                                // from `arr` followed by some junk.
                                                                                // Let's refine this:
  ensures (\forall integer i; 0 <= i < \result ==>
             (\exists integer j; 0 <= j < n && result_arr[i] == arr[j] && is_even_logic(arr[j])));
  ensures (\forall integer j; 0 <= j < n ==>
             (is_even_logic(arr[j]) ==>
                (\exists integer i; 0 <= i < \result && result_arr[i] == arr[j])));
  ensures (\forall integer i; 0 <= i < \result ==> is_even_logic(result_arr[i]));
*/
int filter_even_numbers(int* arr, int n, int* result_arr) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant 0 <= count <= i;
      // Rule II.4: Invariant for the result_arr
      loop invariant \forall integer k; 0 <= k < count ==> is_even_logic(result_arr[k]);
      loop invariant \forall integer k; 0 <= k < count ==>
        (\exists integer j; 0 <= j < i && result_arr[k] == arr[j] && is_even_logic(arr[j]));
      loop invariant \forall integer k; 0 <= k < i ==>
        (is_even_logic(arr[k]) ==>
          (\exists integer l; 0 <= l < count && result_arr[l] == arr[k]));

      loop assigns i, count, result_arr[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // This is the "lambda function" part, checking for evenness.
        // Rule I.2: Using int for boolean logic.
        if (arr[i] % 2 == 0) { // Equivalent to is_even_logic(arr[i])
            result_arr[count] = arr[i];
            count++;
        }
    }
    return count;
}
