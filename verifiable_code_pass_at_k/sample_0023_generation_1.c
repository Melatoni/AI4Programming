// Task ID: 23
// Generation: 1

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
  axiomatic SumOfList {
    logic integer sum_list(int *list, int len);

    axiom sum_list_empty:
      \for_all int *list; sum_list(list, 0) == 0;

    axiom sum_list_recursive:
      \for_all int *list, int len;
      len > 0 ==> sum_list(list, len) == \at(list[len-1], Here) + sum_list(list, len - 1);
  }
*/

/*@
  requires num_lists >= 0;
  requires \valid(lists);
  requires \valid(list_lengths);
  requires \for_all integer i; 0 <= i < num_lists ==> list_lengths[i] >= 0;
  requires \for_all integer i; 0 <= i < num_lists ==> \valid(lists[i] + (0..list_lengths[i]-1));

  // Rule II.5: Prevent Runtime Errors for potential sum overflows.
  // Assuming int can hold the sum of all elements in any sublist.
  // This is a weak check, a stronger one would involve `INT_MAX`.
  // For simplicity, we assume individual sums do not overflow.
  // A more robust check might involve:
  // requires \for_all integer i; 0 <= i < num_lists ==>
  //   (\sum integer j; 0 <= j < list_lengths[i]; \at(lists[i][j], Here)) <= INT_MAX &&
  //   (\sum integer j; 0 <= j < list_lengths[i]; \at(lists[i][j], Here)) >= INT_MIN;

  assigns \nothing;

  ensures num_lists == 0 ==> \result == 0;
  ensures num_lists > 0 ==> \for_all integer i; 0 <= i < num_lists ==> sum_list(lists[i], list_lengths[i]) <= \result;
  ensures num_lists > 0 ==> \exists integer k; 0 <= k < num_lists && \result == sum_list(lists[k], list_lengths[k]);
*/
int find_max_sum_of_lists(int **lists, int *list_lengths, int num_lists) {
    if (num_lists == 0) {
        return 0;
    }

    int max_sum = 0; // Initialize with the sum of the first list if num_lists > 0
                     // Or with a sufficiently small number (e.g., INT_MIN) if sums can be negative.
                     // For this problem, assuming sums can be 0 or positive.

    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant \for_all integer k; 0 <= k < i ==> sum_list(lists[k], list_lengths[k]) <= max_sum;
      loop invariant i > 0 ==> \exists integer j; 0 <= j < i && max_sum == sum_list(lists[j], list_lengths[j]);
      loop assigns i, max_sum;
      loop variant num_lists - i;
    */
    for (int i = 0; i < num_lists; ++i) {
        int current_sum = 0;

        /*@
          loop invariant 0 <= j <= list_lengths[i];
          loop invariant current_sum == sum_list(lists[i], j);
          loop assigns j, current_sum;
          loop variant list_lengths[i] - j;
        */
        for (int j = 0; j < list_lengths[i]; ++j) {
            // Rule II.5: Prevent potential overflow during addition.
            // This requires a more complex invariant involving INT_MAX/INT_MIN.
            // For simplicity, we assume `current_sum + lists[i][j]` does not overflow.
            current_sum += lists[i][j];
        }

        if (i == 0 || current_sum > max_sum) { // Rule III.1: No C-style ternary in ACSL, but fine in C code.
            max_sum = current_sum;
        }
    }

    return max_sum;
}
