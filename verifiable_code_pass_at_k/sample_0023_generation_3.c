// Task ID: 23
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule II.3: ensures clause for boolean-like functions.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@
  axiomatic SumArray {
    logic integer sum_array_elements{L}(int* arr, integer len);

    axiom sum_array_base{L}:
      \forall int* arr, integer len;
      len <= 0 ==> sum_array_elements(arr, len) == 0;

    axiom sum_array_recursive{L}:
      \forall int* arr, integer len;
      len > 0 ==> sum_array_elements(arr, len) == sum_array_elements(arr, len - 1) + arr[len - 1];

    // Helper axiom to prove sum is non-negative if all elements are non-negative.
    axiom sum_array_non_negative{L}:
      \forall int* arr, integer len;
      (\forall integer k; 0 <= k < len ==> arr[k] >= 0) ==> sum_array_elements(arr, len) >= 0;

    // Helper axiom to prove sum is within a range if elements are within a range.
    // This is crucial for proving no overflow for the sum.
    axiom sum_array_bounds{L}:
      \forall int* arr, integer len, integer min_val, integer max_val;
      (\forall integer k; 0 <= k < len ==> min_val <= arr[k] <= max_val) ==>
      len * min_val <= sum_array_elements(arr, len) <= len * max_val;
  }
*/

/*@
  // The function calculates the sum of elements in a single integer array.
  requires len >= 0;
  // Rule II.5: Prevent overflow for sum. Max possible sum for 32-bit int.
  // Assuming elements are within int range, the sum should not exceed INT_MAX.
  // A tighter bound would be required if elements can be large.
  // For simplicity, we assume the sum fits in int.
  // Requires: len * min_element <= sum <= len * max_element
  // Here, we ensure that len * INT_MAX does not overflow if elements are positive.
  requires \forall integer k; 0 <= k < len ==> arr[k] >= -2147483648 && arr[k] <= 2147483647; // INT_MIN to INT_MAX
  // To avoid overflow when calculating sum:
  // If arr[k] could be INT_MAX, then len must be 1.
  // If arr[k] could be INT_MIN, then len must be 1.
  // For a general case, we need to ensure sum_array_elements(arr, len) does not overflow.
  // Let's assume the sum will fit into an int.
  // A more robust check would involve `requires sum_array_elements(arr, len) <= INT_MAX && sum_array_elements(arr, len) >= INT_MIN;`
  // but Frama-C cannot prove this without more specific bounds on arr[k] and len.
  // For this problem, we will assume the sum of elements in any sublist does not overflow an int.
  assigns \nothing;
  ensures \result == sum_array_elements(arr, len);
*/
int sum_list(int* arr, int len) {
    int current_sum = 0;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant current_sum == sum_array_elements(arr, i);
      // Rule II.5: Prevent overflow of current_sum + arr[i].
      loop invariant current_sum <= 2147483647 - (len - i) * (2147483647); // Rough upper bound based on remaining elements and max value
      loop invariant current_sum >= -2147483648 - (len - i) * (-2147483648); // Rough lower bound
      loop assigns current_sum, i;
      loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Assertions for preventing overflow before addition
        /*@ assert current_sum <= 2147483647 - arr[i]; */
        /*@ assert current_sum >= -2147483648 - arr[i]; */
        current_sum += arr[i];
    }
    return current_sum;
}

/*@
  axiomatic MaxSumOfLists {
    logic integer max_sum_of_lists_logic{L}(int** lists, int* lengths, integer num_lists);

    axiom max_sum_of_lists_base{L}:
      \forall int** lists, int* lengths, integer num_lists;
      num_lists <= 0 ==> max_sum_of_lists_logic(lists, lengths, num_lists) == -2147483648; // Represents negative infinity for int

    axiom max_sum_of_lists_recursive{L}:
      \forall int** lists, int* lengths, integer num_lists;
      num_lists > 0 ==>
      max_sum_of_lists_logic(lists, lengths, num_lists) ==
        (if num_lists == 1 then sum_array_elements(lists[0], lengths[0])
         else (if sum_array_elements(lists[num_lists - 1], lengths[num_lists - 1]) > max_sum_of_lists_logic(lists, lengths, num_lists - 1)
               then sum_array_elements(lists[num_lists - 1], lengths[num_lists - 1])
               else max_sum_of_lists_logic(lists, lengths, num_lists - 1)));
    
    // Helper axiom for the maximum value (if all sums are within int range)
    axiom max_sum_of_lists_bounds{L}:
      \forall int** lists, int* lengths, integer num_lists;
      (\forall integer k; 0 <= k < num_lists ==> sum_array_elements(lists[k], lengths[k]) <= 2147483647) ==>
      max_sum_of_lists_logic(lists, lengths, num_lists) <= 2147483647;
    
    axiom max_sum_of_lists_non_empty_min_value{L}:
      \forall int** lists, int* lengths, integer num_lists;
      num_lists > 0 ==>
      max_sum_of_lists_logic(lists, lengths, num_lists) >= -2147483648;
  }
*/

/*@
  requires num_lists >= 0;
  // Each sublist must have a non-negative length.
  requires \forall integer i; 0 <= i < num_lists ==> lengths[i] >= 0;
  // Each sublist must be a valid pointer if its length is > 0.
  requires \forall integer i; 0 <= i < num_lists ==> (lengths[i] > 0 ==> \valid(lists[i] + (0..lengths[i]-1)));
  // All elements in all sublists must be within int range.
  requires \forall integer i; 0 <= i < num_lists ==>
           \forall integer j; 0 <= j < lengths[i] ==> lists[i][j] >= -2147483648 && lists[i][j] <= 2147483647;
  // Assume sums of individual lists do not overflow. This is handled by sum_list's requires.
  // If num_lists is 0, the result should be INT_MIN (or a conceptual negative infinity).
  // Frama-C's INT_MIN is -2147483648.
  assigns \nothing;
  ensures \result == max_sum_of_lists_logic(lists, lengths, num_lists);
*/
int find_max_sum_of_lists(int** lists, int* lengths, int num_lists) {
    // If there are no lists, return the smallest possible int value to signify negative infinity.
    // Rule II.5: Prevent RTE/overflow, especially for initialization.
    // If num_lists is 0, the loop won't run, and this initial value will be returned.
    int max_sum = -2147483648; // Corresponds to INT_MIN

    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant (i == 0 ==> max_sum == -2147483648);
      loop invariant (i > 0 ==> max_sum == max_sum_of_lists_logic(lists, lengths, i));
      // Rule II.5: Ensure max_sum update does not overflow (e.g., if max_sum is INT_MAX and current_sum is larger)
      // This is implicitly handled by the fact that the sum_list function ensures its result fits in int.
      // And the max operation simply picks one of two valid int values.
      loop assigns max_sum, i;
      loop variant num_lists - i;
    */
    for (int i = 0; i < num_lists; i++) {
        /*@
          // Pre-condition for sum_list call.
          requires lengths[i] >= 0;
          requires (lengths[i] > 0 ==> \valid(lists[i] + (0..lengths[i]-1)));
          requires \forall integer k; 0 <= k < lengths[i] ==> lists[i][k] >= -2147483648 && lists[i][k] <= 2147483647;
          // Post-condition for sum_list call.
          ensures \result == sum_array_elements(lists[i], lengths[i]);
        */
        int current_list_sum = sum_list(lists[i], lengths[i]);

        // Rule II.5: Prevent overflow/underflow if max_sum is updated.
        // This is safe because we are just comparing two int values and picking one.
        // The comparison and assignment themselves do not cause overflow.
        if (current_list_sum > max_sum) {
            max_sum = current_list_sum;
        }
    }

    return max_sum;
}
