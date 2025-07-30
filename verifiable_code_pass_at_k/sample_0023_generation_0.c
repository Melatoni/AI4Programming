// Task ID: 23
// Generation: 0

/*@
  // Rule I.1: No standard libraries like <limits.h>. Use ACSL constants.
  // Rule II.5: Prevent potential overflow when summing elements.
  // Assuming a 32-bit signed int, the maximum sum for a sublist
  // is (INT_MAX / max_sublist_length).
  // A conservative estimate for max_sublist_length could be 1000 if not specified.
  // If no specific max length is given, assume it could be large,
  // so individual elements must be constrained to prevent overflow.
  // Let's assume elements max 1000 and max 1000 elements per sublist
  // to avoid overflow for int.
  // If INT_MAX is 2,147,483,647, then 1000 * 1000 = 1,000,000 is fine.
  // For the sum of sums, if there are 1000 sublists, max sum would be 1000 * 1,000,000 = 1,000,000,000, which is also fine.
  // But if elements are near INT_MAX/2, then only 2 elements sum would overflow.
  // So, constrain input elements.
  requires \forall integer i, j; 0 <= i < num_lists && 0 <= j < lengths[i] ==> \abs(lists[i][j]) <= 1000;
  requires \forall integer i; 0 <= i < num_lists ==> lengths[i] >= 0;
  requires num_lists >= 0;
  requires num_lists <= 1000; // Max number of sublists
  requires \forall integer i; 0 <= i < num_lists ==> lengths[i] <= 1000; // Max elements in a sublist

  assigns \nothing;

  // Rule II.1: Recursive logic for summation.
  // Rule I.3: Array pointer decay - T (*arr)[C]
  axiomatic SumList {
    logic integer sum_list(int* list, int len);

    axiom sum_list_base:
      \forall int* list, int len;
        len == 0 ==> sum_list(list, len) == 0;

    axiom sum_list_recursive:
      \forall int* list, int len;
        len > 0 ==> sum_list(list, len) == list[len - 1] + sum_list(list, len - 1);

    // Rule II.2: Helper axiom for sum_list to reason about its bounds.
    // If all elements are within [-M, M], then sum is within [-M*len, M*len].
    axiom sum_list_bounds:
      \forall int* list, int len, integer M;
        (\forall integer k; 0 <= k < len ==> \abs(list[k]) <= M) ==>
        \abs(sum_list(list, len)) <= M * len;
  }

  // Rule II.5: The maximum possible sum of a single sublist.
  // Max possible sum is 1000 * 1000 = 1,000,000.
  // This value fits within a 32-bit signed integer.
  // The overall max sum can be num_lists * (max_sublist_sum).
  // 1000 * 1,000,000 = 1,000,000,000, which also fits.
  // So, no explicit requires for sum overflow needed beyond element constraints.

  // The function returns the maximum sum found among all sublists.
  // If num_lists is 0, the result should be a reasonable value for "no sum",
  // e.g., the smallest possible integer, or some indicator.
  // For this problem, let's assume if num_lists is 0, the sum is 0
  // (or the first sum encountered is the max).
  // If num_lists > 0, then the result must be one of the sublist sums.
  ensures num_lists == 0 ==> \result == 0; // Or some other defined behavior.
  ensures num_lists > 0 ==>
    (\exists integer i; 0 <= i < num_lists && \result == sum_list(lists[i], lengths[i]));
  ensures num_lists > 0 ==>
    (\forall integer i; 0 <= i < num_lists ==> \result >= sum_list(lists[i], lengths[i]));
*/
int find_max_sublist_sum(int* lists[], int* lengths, int num_lists) {
    if (num_lists == 0) {
        return 0; // Defined behavior for empty input
    }

    // Initialize max_sum with the sum of the first sublist.
    // This assumes num_lists > 0.
    int max_sum = 0;
    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant \forall integer k; 0 <= k < i ==>
        // Rule II.5: Check for potential overflow before `max_sum = sum_list(...)`
        // The sum_list_bounds axiom helps here.
        // max_sum will hold the maximum sum encountered so far.
        // The individual sums are already constrained by initial requires.
        // sum_list(lists[k], lengths[k]) fits in int.
        // The comparison doesn't overflow.
        max_sum >= sum_list(lists[k], lengths[k]);
      loop invariant i > 0 ==>
        (\exists integer k; 0 <= k < i && max_sum == sum_list(lists[k], lengths[k]));
      loop assigns i, max_sum;
      loop variant num_lists - i;
    */
    for (int i = 0; i < num_lists; ++i) {
        int current_sum = 0;
        /*@
          loop invariant 0 <= j <= lengths[i];
          loop invariant current_sum == sum_list(lists[i], j);
          loop assigns j, current_sum;
          loop variant lengths[i] - j;
        */
        for (int j = 0; j < lengths[i]; ++j) {
            // Rule II.5: Prevent overflow during summation for current_sum.
            // Based on initial requires (\abs(lists[i][j]) <= 1000) and lengths[i] <= 1000,
            // current_sum can be at most 1,000 * 1,000 = 1,000,000, which fits in int.
            current_sum += lists[i][j];
        }

        if (i == 0 || current_sum > max_sum) {
            max_sum = current_sum;
        }
    }

    return max_sum;
}
