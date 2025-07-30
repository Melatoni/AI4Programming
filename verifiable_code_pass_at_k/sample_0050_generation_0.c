// Task ID: 50
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in axiomatic blocks if needed.

  // Rule II.1, II.2: Recursive logic and helper axioms are not directly needed for this problem,
  // as it's about finding a minimum length, not complex summations or properties over sequences.

  // Rule II.5: Prevent Runtime Errors.
  // The problem statement implies an array of arrays (or a 2D array if we fix dimensions).
  // We need to constrain the maximum number of lists and their maximum lengths to prevent
  // potential integer overflows if lengths were summed or used in large products.
  // For this problem, we are just comparing lengths, so overflow on lengths themselves
  // is less likely unless the lengths are extremely large (e.g., > INT_MAX).
  // We assume lengths are within 'int' range.
  // The number of lists 'num_lists' and the 'max_list_length' must be non-negative.
  requires num_lists >= 0;
  requires max_list_length >= 0; // Represents the maximum possible length of any list.

  // The function finds the index of the list with the minimum length.
  // If `num_lists` is 0, it should indicate an error or a special case.
  // We define 
  OT_FOUND as -1 to indicate no list found.
  // This is a common pattern for "not found" results.
*/
#define NOT_FOUND -1

/*@
  // Rule II.1, II.2: For this problem, we don't need complex recursive logic.
  // We're finding a minimum, which can be expressed iteratively.

  // Predicate to check if a given index 'idx' corresponds to the minimum length list.
  // This helps make the post-condition more readable and verifiable.
  logic boolean is_min_length_index{L}(int idx, int num_lists, int* list_lengths) =
    idx >= 0 && idx < num_lists &&
    (\forall integer k; 0 <= k < num_lists ==> list_lengths[idx] <= list_lengths[k]);

  // Predicate to check if all lengths are non-negative.
  // This is a reasonable assumption for "lengths".
  logic boolean all_lengths_non_negative{L}(int num_lists, int* list_lengths) =
    \forall integer k; 0 <= k < num_lists ==> list_lengths[k] >= 0;
*/

/*@
  requires num_lists >= 0;
  // Rule II.5: Ensure list_lengths array is valid for num_lists elements.
  requires \valid_read(list_lengths + (0..num_lists - 1));
  requires all_lengths_non_negative(num_lists, list_lengths);

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // If num_lists is 0, the result should be NOT_FOUND.
  // Otherwise, the result should be a valid index corresponding to a minimum length list.
  ensures (num_lists == 0) ==> (esult == NOT_FOUND);
  ensures (num_lists > 0) ==> (is_min_length_index(esult, num_lists, list_lengths));
*/
int find_min_length_list_index(int num_lists, int* list_lengths) {
    if (num_lists == 0) {
        return NOT_FOUND;
    }

    int min_len = list_lengths[0];
    int min_idx = 0;

    /*@
      loop invariant 0 <= i <= num_lists;
      loop invariant 0 <= min_idx < i; // min_idx is always an index of an element processed so far
      loop invariant min_len == list_lengths[min_idx]; // min_len is the length at min_idx
      // min_len is the minimum length found so far among elements 0 to i-1
      loop invariant \forall integer k; 0 <= k < i ==> list_lengths[min_idx] <= list_lengths[k];
      loop assigns i, min_len, min_idx;
      // Rule II.4: A loop variant is mandatory for termination.
      loop variant num_lists - i;
    */
    for (int i = 1; i < num_lists; i++) {
        // Rule II.5: Prevent potential out-of-bounds access if list_lengths was not properly validated.
        // This is covered by the function's requires clause: \valid_read(list_lengths + (0..num_lists - 1));
        if (list_lengths[i] < min_len) {
            min_len = list_lengths[i];
            min_idx = i;
        }
    }

    return min_idx;
}

/*@
  // Example usage (not part of the function to be verified, but for context)
  // This part would typically be in a test harness or main function.

  // A 2D array of variable length lists would typically be represented as an array
  // of pointers to arrays, or an array of structs containing a pointer and a length.
  // For simplicity and to fit the problem statement's "list with minimum length",
  // we assume we are given an array of lengths directly.
  // The "lambda function" part of the problem implies that the comparison logic
  // (i.e., comparing lengths) is supplied or inherent. Our function directly
  // implements this comparison.

  // Let's define a helper for the main function's purpose.
  // We need to define the concept of a "list" which has a length.
  // Since we are given an array of lengths, we can assume each element of
  // `list_lengths` corresponds to the length of a "list".
*/

/*@
  // Main function is typically not verified directly in Frama-C/WP,
  // but it's good practice to have a simple entry point.
  // This main function is illustrative and not subject to the strict
  // verification rules of the `find_min_length_list_index` function.
  // It's here to show how the function might be used.
*/
// int main() {
//     // Example 1: Standard case
//     int lengths1[] = {5, 2, 8, 1, 9};
//     int num_lists1 = 5;
//     int min_idx1 = find_min_length_list_index(num_lists1, lengths1);
//     // Expected: min_idx1 == 3 (length 1)

//     // Example 2: Empty list of lists
//     int lengths2[] = {};
//     int num_lists2 = 0;
//     int min_idx2 = find_min_length_list_index(num_lists2, lengths2);
//     // Expected: min_idx2 == NOT_FOUND (-1)

//     // Example 3: Single list
//     int lengths3[] = {10};
//     int num_lists3 = 1;
//     int min_idx3 = find_min_length_list_index(num_lists3, lengths3);
//     // Expected: min_idx3 == 0 (length 10)

//     // Example 4: Duplicate minimums
//     int lengths4[] = {5, 2, 8, 2, 9};
//     int num_lists4 = 5;
//     int min_idx4 = find_min_length_list_index(num_lists4, lengths4);
//     // Expected: min_idx4 == 1 (first occurrence of length 2)

//     return 0;
// }
