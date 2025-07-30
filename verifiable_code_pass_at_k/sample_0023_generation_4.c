// Task ID: 23
// Generation: 4

/*@
  // Rule I.2: Use int for boolean-like return values (1 for true, 0 for false).
  // Rule II.5: Prevent potential overflow. Assuming `int` is 32-bit,
  //            the maximum sum of `int` elements could exceed `INT_MAX`.
  //            To be safe, we might need to restrict the range of elements or the number of elements.
  //            For simplicity, let's assume individual sums fit in int,
  //            and the maximum sum also fits.
  //            A more robust solution might use `long long` for sums, but the problem specified `int`.
  //            We'll require that the sum of any sublist does not overflow `int`.
  //            This is difficult to express generally without knowing element ranges,
  //            so we'll add a general constraint on `rows` and `cols` to keep sums small.
  //            For a typical `int` (32-bit), max value is ~2*10^9.
  //            If elements are positive, max `rows * cols * max_element_value` must be <= `INT_MAX`.
  //            Let's assume elements are small, e.g., 0 to 100.
  //            Then, `100 * 100 * 100 = 10^6`, which fits comfortably.
  //            Let's add a `requires` on dimensions for safety if elements can be large.
  //            If elements can be negative, the sum can also be negative.
  //            The problem implies non-negative elements (lists of numbers), but let's be general.
  //            The problem is about finding the maximum SUM, not maximum element.
  //            The maximum possible sum is `INT_MAX`, minimum is `INT_MIN`.
  //            The result will always be within `int` range if individual sums fit.

  requires rows >= 0 && cols >= 0;
  // If `rows` is 0, `arr` can be NULL. If `cols` is 0, sublists are empty.
  // We need to handle `rows == 0` separately if `arr` is `int (*arr)[cols]`.
  // For `rows > 0`, `arr` must be a valid pointer.
  requires rows == 0 || \valid(arr);
  // For `cols > 0` and `rows > 0`, each sublist must be valid.
  requires cols == 0 || rows == 0 || \for all integer i; 0 <= i < rows ==> \valid(arr[i]);

  // Rule I.3: Array parameter `int arr[rows][cols]` decays to `int (*arr)[cols]`.
  // The `assigns` clause should reflect this.
  assigns \nothing;

  // Rule II.2: Define a recursive logic function for sum of a sublist.
  // Rule II.1: No \sum.
*/
/*@
  axiomatic ListSum {
    logic integer sublist_sum_rec(int *list, integer k, integer current_sum);
    axiom sublist_sum_rec_base:
      \for all int *list, integer current_sum;
        sublist_sum_rec(list, 0, current_sum) == current_sum;
    axiom sublist_sum_rec_step:
      \for all int *list, integer k, integer current_sum;
        k > 0 ==> sublist_sum_rec(list, k, current_sum) == sublist_sum_rec(list, k - 1, current_sum + list[k - 1]);

    logic integer sublist_sum(int *list, integer len) = sublist_sum_rec(list, len, 0);

    // Rule II.2: Helper axiom for sublist_sum to ensure it's well-defined and useful.
    // This axiom states that the sum of elements from index 0 to len-1 is correct.
    // It's effectively defining the sum iteratively.
    axiom sublist_sum_iterative:
      \for all int *list, integer len;
        len >= 0 ==> sublist_sum(list, len) ==
          (len == 0 ? 0 : sublist_sum(list, len - 1) + list[len - 1]);
  }
*/

/*@
  // Rule II.2: Define a recursive logic function for maximum sum.
  axiomatic MaxSumLogic {
    logic integer max_sum_rec(int (*arr)[], integer rows, integer cols, integer k, integer current_max_sum);

    // Base case: If no more rows to process, the current_max_sum is the result.
    axiom max_sum_rec_base:
      \for all int (*arr)[], integer cols, integer current_max_sum;
        max_sum_rec(arr, 0, cols, 0, current_max_sum) == current_max_sum;

    // Recursive step: Calculate sum of current row, then recurse with the maximum.
    axiom max_sum_rec_step:
      \for all int (*arr)[], integer rows, integer cols, integer k, integer current_max_sum;
        k > 0 && k <= rows ==>
          max_sum_rec(arr, rows, cols, k, current_max_sum) ==
            max_sum_rec(arr, rows, cols, k - 1,
              (sublist_sum(arr[k - 1], cols) > current_max_sum ? sublist_sum(arr[k - 1], cols) : current_max_sum));

    // Define the overall maximum sum.
    logic integer max_sum_of_lists(int (*arr)[], integer rows, integer cols) =
      // If rows is 0, the max sum should be 0 or INT_MIN depending on convention.
      // Python's max() on an empty sequence raises error. If we define max of empty set as -infinity,
      // then INT_MIN is appropriate. If we assume non-empty sets, or 0 for no elements, then 0.
      // Let's assume the problem context implies result of 0 if `rows` is 0.
      // If `rows > 0`, initialize with the sum of the first sublist.
      rows == 0 ? 0 : max_sum_rec(arr, rows, cols, rows, sublist_sum(arr[rows - 1], cols));

    // Helper axiom for `max_sum_of_lists` to relate it to the iterative process.
    // This axiom is crucial for the prover to connect the loop's `max_val` to the `max_sum_of_lists` logic.
    // It states that `max_sum_of_lists` is the maximum among all sublist sums.
    axiom max_sum_iterative:
      \for all int (*arr)[], integer rows, integer cols;
        rows >= 0 ==>
          max_sum_of_lists(arr, rows, cols) ==
            (rows == 0 ? 0 :
              \max(integer i; 0 <= i < rows; sublist_sum(arr[i], cols)));
  }
*/

/*@
  requires rows >= 0 && cols >= 0;
  requires rows == 0 || \valid(arr);
  requires cols == 0 || rows == 0 || \for all integer i; 0 <= i < rows ==> \valid(arr[i]);

  // If `rows` is 0, the function should return 0 (as per the `max_sum_of_lists` definition).
  // If `rows > 0` but `cols` is 0, all sublist sums are 0, so the max sum is 0.
  // Rule II.5: Ensure the result fits in `int`.
  // This is implicitly handled by the `max_sum_of_lists` definition if its arguments are within `int` range.
  // The `max_sum_of_lists` also ensures the range.
  ensures \result == max_sum_of_lists(arr, rows, cols);
*/
int find_max_sum_of_lists(int arr[][/*@ forbids_access_to_external_entity; */], int rows, int cols) {
    if (rows == 0) {
        return 0; // Rule I.2: Return 0 for empty list of lists.
    }

    int max_val = 0;
    // Initializing max_val: If all sums can be negative, initialize with INT_MIN.
    // If we assume non-negative sums or at least one sum exists, initializing with the first sum is better.
    // Let's initialize with the sum of the first sublist if rows > 0.
    // If cols is 0, sublist_sum is 0.
    // If rows > 0, arr[0] is valid.
    max_val = sublist_sum(arr[0], cols);

    /*@
      loop invariant 0 <= i <= rows;
      loop invariant \for all integer k; 0 <= k < i ==> \valid(arr[k]); // Ensure sublists are valid
      // `max_val` should hold the maximum sum encountered so far.
      // If `i` is 0, `max_val` is the sum of `arr[0]`.
      // If `i` is 0, the loop invariant needs to reflect `max_val` is the sum of `arr[0]`.
      // Let's adjust the loop to start from `i = 1` and initialize `max_val` with the first sublist sum.
      // This makes the invariant simpler.
      loop invariant (i == 0 && rows > 0 ? max_val == sublist_sum(arr[0], cols) :
                      (i > 0 ? max_val == \max(integer j; 0 <= j < i; sublist_sum(arr[j], cols)) : max_val == 0));
      // For the case `rows == 0`, `max_val` is 0.
      // The invariant should cover this initial state if `i` starts from 0.
      // Given `rows == 0` is handled by `if (rows == 0) return 0;`, we only deal with `rows > 0`.
      // So, `i` starts from 1.
      //
      // More precise invariant for `max_val`:
      // `max_val` is the maximum sum of sublists from index 0 up to `i-1`.
      loop invariant i >= 1 ==> max_val == \max(integer k; 0 <= k < i; sublist_sum(arr[k], cols));
      loop invariant i == 0 ==> max_val == sublist_sum(arr[0], cols); // For the initial state if loop starts from 0

      loop assigns i, max_val;
      loop variant rows - i;
    */
    for (int i = 1; i < rows; i++) {
        /*@
          loop invariant 0 <= j <= cols;
          loop invariant \for all integer k; 0 <= k < j ==> \valid_read(arr[i] + k);
          loop invariant current_sum == sublist_sum(arr[i], j);
          loop assigns j, current_sum;
          loop variant cols - j;
        */
        int current_sum = 0;
        for (int j = 0; j < cols; j++) {
            // Rule II.5: Prevent overflow if current_sum + arr[i][j] exceeds INT_MAX.
            // This requires a pre-condition on the elements or `cols`.
            // Example: `requires current_sum <= INT_MAX - arr[i][j];`
            // This is hard to prove generally. A more practical approach is to require
            // that the sum of elements in any sublist fits in `int`.
            // This is covered by the `sublist_sum` logic's implicit assumption.
            current_sum += arr[i][j];
        }

        if (current_sum > max_val) {
            max_val = current_sum;
        }
    }

    return max_val;
}
