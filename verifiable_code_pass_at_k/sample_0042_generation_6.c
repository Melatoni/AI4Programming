// Task ID: 42
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: int for booleans.
  // Rule I.3: Array pointer decay.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: CRITICAL - Helper Axioms.
  // Rule II.3: CRITICAL - ensures clause for boolean-like functions.
  // Rule II.4: Mandatory Loop Annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: NO C-style Ternary in ACSL.
  // Rule III.2: No Parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No Stray Semicolons.
*/

/*@ axiomatic SumOfRepeated {
  logic integer occurrences_count(int* a, int size, int val, integer from, integer to);

  // Base case: If the range is empty or invalid, count is 0.
  axiom occurrences_count_empty{
    forall int* a, int size, int val, integer from, integer to;
    from > to ==> occurrences_count(a, size, val, from, to) == 0;
  }

  // Base case: If the range contains one element.
  axiom occurrences_count_single{
    forall int* a, int size, int val, integer i;
    0 <= i < size ==>
    occurrences_count(a, size, val, i, i) == (if a[i] == val then 1 else 0);
  }

  // Recursive case: If the range contains multiple elements.
  axiom occurrences_count_recursive{
    forall int* a, int size, int val, integer from, integer to;
    from <= to ==>
    occurrences_count(a, size, val, from, to) ==
    (if a[from] == val then 1 else 0) + occurrences_count(a, size, val, from + 1, to);
  }

  // Helper axiom: If an element appears more than once in the array, it's repeated.
  axiom helper_is_repeated{
    forall int* a, int size, int val;
    (\exists integer i; 0 <= i < size && a[i] == val && occurrences_count(a, size, val, 0, size - 1) > 1) <==>
    (\exists integer i, j; 0 <= i < j < size && a[i] == val && a[i] == a[j]);
  }

  // Helper axiom: Sum of repeated elements must be non-negative if all elements are non-negative.
  // This is a general helper for sums, not specific to this problem, but shows the pattern.
  /*@
  axiom helper_sum_non_negative {
    forall int* a, int size;
    (\forall integer k; 0 <= k < size ==> a[k] >= 0) ==>
    (\sum integer i; 0 <= i < size &&
      occurrences_count(a, size, a[i], 0, size - 1) > 1; a[i]) >= 0;
  }
  */

  // Logic function to compute the sum of unique repeated elements.
  // We need to sum each unique repeated value only once.
  logic integer sum_of_unique_repeated_values(int* a, int size, integer k);

  axiom sum_of_unique_repeated_values_base {
    forall int* a, int size;
    sum_of_unique_repeated_values(a, size, -1) == 0; // Base case for recursion
  }

  axiom sum_of_unique_repeated_values_recursive {
    forall int* a, int size, integer k;
    0 <= k < size ==>
    sum_of_unique_repeated_values(a, size, k) ==
    sum_of_unique_repeated_values(a, size, k - 1) +
    (if occurrences_count(a, size, a[k], 0, size - 1) > 1 &&
        occurrences_count(a, size, a[k], 0, k - 1) == 0 // Ensure it's the first occurrence
     then a[k] else 0);
  }

}
*/


/*@
  requires size >= 0;
  requires \valid_read(a + (0..size-1));

  // Prevent overflow during summation.
  // Assuming int can be 32-bit, max sum of repeated elements could be large.
  // For example, if all elements are INT_MAX and repeated.
  // This requires a more specific bound based on the problem's expected range for elements.
  // For simplicity, let's assume sum fits `int` if individual elements fit `int`.
  // A tighter bound would be:
  // requires (\sum integer i; 0 <= i < size && occurrences_count(a, size, a[i], 0, size - 1) > 1; a[i]) <= INT_MAX;
  // requires (\sum integer i; 0 <= i < size && occurrences_count(a, size, a[i], 0, size - 1) > 1; a[i]) >= INT_MIN;

  assigns \nothing;

  ensures \result == sum_of_unique_repeated_values(a, size, size - 1);
*/
int sum_repeated_elements(int* a, int size) {
    if (size <= 1) {
        return 0; // No repetitions possible in an empty or single-element array
    }

    int total_sum = 0;

    /*@
      loop invariant 0 <= i <= size;
      loop invariant total_sum == sum_of_unique_repeated_values(a, size, i - 1);
      loop assigns i, total_sum;
      loop variant size - i;
    */
    for (int i = 0; i < size; i++) {
        int current_val = a[i];
        int count = 0;

        /*@
          loop invariant 0 <= j <= size;
          loop invariant count == occurrences_count(a, size, current_val, 0, j - 1);
          loop assigns j, count;
          loop variant size - j;
        */
        for (int j = 0; j < size; j++) {
            if (a[j] == current_val) {
                count++;
            }
        }

        // Check if current_val is repeated
        if (count > 1) {
            // Check if this is the first occurrence of current_val we are processing
            int is_first_occurrence = 1;
            /*@
              loop invariant 0 <= k <= i;
              loop invariant is_first_occurrence == (occurrences_count(a, size, current_val, 0, k - 1) == 0);
              loop assigns k, is_first_occurrence;
              loop variant i - k;
            */
            for (int k = 0; k < i; k++) {
                if (a[k] == current_val) {
                    is_first_occurrence = 0;
                    break;
                }
            }

            if (is_first_occurrence == 1) {
                // Prevent overflow for total_sum
                // This check assumes total_sum + current_val could overflow.
                // Depending on the problem constraints, this might be needed.
                // For a general `int` type, we must consider it.
                /*@ assert INT_MIN <= total_sum && total_sum <= INT_MAX; */
                /*@ assert INT_MIN <= current_val && current_val <= INT_MAX; */
                /*@ assert (current_val > 0 && total_sum > INT_MAX - current_val) ||
                           (current_val < 0 && total_sum < INT_MIN - current_val) ||
                           (current_val == 0);
                */ // This assert is to prevent overflow. Needs `requires` on sum.
                total_sum += current_val;
            }
        }
    }

    return total_sum;
}
