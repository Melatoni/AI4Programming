// Task ID: 41
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  // Define a type for the "lambda function" (a function pointer)
  // This is how Frama-C handles function pointers in specifications.
  // The 'int' return type and 'int' parameter match the expected signature
  // for an even number check: int is_even(int x).
  typedef int (*filter_predicate)(int);

  // Axiomatic block to define properties of the filter_predicate
  // Specifically, we define what it means for a predicate to be an "is_even" function.
  axiomatic EvenPredicate {
    logic boolean is_even_predicate(filter_predicate p);

    // Axiom: A predicate 'p' is an "is_even" predicate if for any integer 'x',
    // p(x) returns 1 if x is even, and 0 if x is odd.
    axiom is_even_def:
      \forall integer x;
        is_even_predicate(p) ==>
          ( (x % 2 == 0) <==> (p(x) == 1) );
  }

  // Axiomatic block for the filtered array logic
  axiomatic FilteredArray {
    logic integer[] filtered_elements{L}(int* arr, integer len, filter_predicate p);
    logic integer filtered_count{L}(int* arr, integer len, filter_predicate p);

    // Base case for filtered_elements: empty array yields an empty sequence
    axiom filtered_elements_empty:
      filtered_elements(arr, 0, p) == \seq_empty;

    // Recursive case for filtered_elements:
    // If the first element satisfies the predicate, it's prepended to the filtered sequence of the rest.
    // Otherwise, it's skipped.
    axiom filtered_elements_recursive:
      \forall int* arr, integer len, filter_predicate p;
        len > 0 ==>
          filtered_elements(arr, len, p) ==
            (if p(arr[0]) == 1
             then \seq_cons(arr[0], filtered_elements(arr + 1, len - 1, p))
             else filtered_elements(arr + 1, len - 1, p));

    // Base case for filtered_count: empty array has 0 filtered elements
    axiom filtered_count_empty:
      filtered_count(arr, 0, p) == 0;

    // Recursive case for filtered_count:
    // If the first element satisfies the predicate, increment count and recurse.
    // Otherwise, just recurse.
    axiom filtered_count_recursive:
      \forall int* arr, integer len, filter_predicate p;
        len > 0 ==>
          filtered_count(arr, len, p) ==
            (if p(arr[0]) == 1
             then 1 + filtered_count(arr + 1, len - 1, p)
             else filtered_count(arr + 1, len - 1, p));

    // Helper axiom: The length of the filtered elements sequence is equal to the filtered count.
    axiom filtered_length_matches_count:
      \forall int* arr, integer len, filter_predicate p;
        \seq_length(filtered_elements(arr, len, p)) == filtered_count(arr, len, p);
  }
*/

/*@
  // Predicate function for checking if a number is even.
  // This function will be passed as the 'lambda function'.
  assigns \nothing;
  ensures (x % 2 == 0) <==> (esult == 1);
*/
int is_even(int x) {
    if (x % 2 == 0) {
        return 1;
    }
    return 0;
}

/*@
  // Requires:
  // - The input array 'arr' must be allocated for at least 'len' elements.
  // - 'len' must be non-negative.
  // - 'filter_func' must be an "is_even" predicate as defined by our axiomatic.
  requires \valid_read_array(arr, 0..len-1);
  requires len >= 0;
  requires is_even_predicate(filter_func);

  // Assigns:
  // - The function writes to the 'result_arr' up to 'result_len' elements.
  // - It assigns to '*result_len' to store the actual number of filtered elements.
  assigns result_arr[0..*result_len - 1], *result_len;

  // Ensures:
  // - The number of elements written to 'result_arr' is exactly the count
  //   of even numbers in the original 'arr'.
  // - All elements in 'result_arr' are even.
  // - All elements in 'result_arr' are present in the original 'arr'.
  // - The order of elements is preserved.
  ensures *result_len == filtered_count(arr, len, filter_func);

  ensures \forall integer k; 0 <= k < *result_len ==> result_arr[k] % 2 == 0;

  // Ensures the content of result_arr matches the filtered_elements sequence.
  ensures \forall integer k; 0 <= k < *result_len ==> result_arr[k] == \seq_get(filtered_elements(arr, len, filter_func), k);
*/
void filter_even_numbers(int* arr, int len, int* result_arr, int* result_len, /*@ type filter_predicate */ int (*filter_func)(int)) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= len;
      loop invariant 0 <= count <= i;
      // Invariant: 'count' holds the number of even elements found so far in arr[0..i-1].
      loop invariant count == filtered_count(arr, i, filter_func);
      // Invariant: 'result_arr' contains exactly the filtered elements from arr[0..i-1].
      loop invariant \forall integer k; 0 <= k < count ==> result_arr[k] == \seq_get(filtered_elements(arr, i, filter_func), k);
      loop assigns i, count, result_arr[0..len-1]; // result_arr can be written up to len elements.
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Call the "lambda function" (filter_func)
        if (filter_func(arr[i]) == 1) {
            /*@
              // Precondition check for array write: ensure there's enough space.
              // We know count <= i < len, so result_arr[count] is within result_arr[0..len-1].
              assert count < len;
            */
            result_arr[count] = arr[i];
            count++;
        }
    }

    *result_len = count;
}
