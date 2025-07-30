// Task ID: 13
// Generation: 2

/*@
  // Rule I.1: No standard libraries.
  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms.
  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  // Axiomatic block for recursive logic to define properties of arrays.
  axiomatic ArrayProperties {
    // Defines the maximum value in a given range of an integer array.
    logic integer max_in_range(int *arr, integer start, integer end);

    // Base case: If the range is empty or invalid, max is undefined (or a suitable default).
    // For simplicity, we assume start <= end. If start > end, this is not well-defined.
    axiom max_in_range_base{L}(int *arr, integer start, integer end) =
      start == end ==> max_in_range(arr, start, end) == arr[start];

    // Recursive case: Max of a range is max of first element and max of rest.
    axiom max_in_range_rec{L}(int *arr, integer start, integer end) =
      start < end ==> max_in_range(arr, start, end) ==
        (if arr[start] > max_in_range(arr, start + 1, end) then arr[start] else max_in_range(arr, start + 1, end));

    // Helper axiom: If all elements are non-negative, max_in_range is non-negative.
    // This can be useful if counts are always non-negative.
    axiom max_in_range_non_negative{L}(int *arr, integer start, integer end) =
      (\forall integer k; start <= k <= end ==> arr[k] >= 0) ==> max_in_range(arr, start, end) >= 0;

    // Helper axiom: The maximum value returned by max_in_range is indeed one of the elements
    // within the specified range.
    axiom max_in_range_exists{L}(int *arr, integer start, integer end) =
      (\exists integer k; start <= k <= end && max_in_range(arr, start, end) == arr[k]);

    // Helper axiom: Any element in the range is less than or equal to the maximum of the range.
    axiom max_in_range_upper_bound{L}(int *arr, integer start, integer end) =
      (\forall integer k; start <= k <= end ==> arr[k] <= max_in_range(arr, start, end));
  }
*/

/*@
  requires num_words >= 0;
  requires num_distinct_words >= 0;
  // Ensure that word_counts array is large enough to hold counts for num_distinct_words.
  requires \valid_read(word_counts + (0..num_distinct_words - 1));
  // Ensure that the k parameter is valid.
  requires k >= 0;

  // Rule II.5: Prevent potential overflow if k is very large, though counts are generally small.
  // This is more about loop termination and array bounds.
  // If k is greater than num_distinct_words, we select all distinct words.
  // We assume counts are non-negative.
  requires \forall integer i; 0 <= i < num_distinct_words ==> word_counts[i] >= 0;

  assigns \nothing;

  // Rule II.3: Ensures clause using logical equivalence.
  // The function returns the maximum count among the top k most common words.
  // This problem description is slightly ambiguous about "count the most common words".
  // A common interpretation is to find the minimum count among the top K words
  // (i.e., any word with a count >= this value is considered "most common").
  // Another interpretation is to return the K-th largest count.
  // For this exercise, let's interpret "count the most common words" as
  // finding the K-th largest frequency, which defines the threshold for "most common".
  // If k = 0, no words are "most common", so the threshold could be arbitrarily high (e.g., INT_MAX or 0 if no words).
  // If k > num_distinct_words, it means we consider all words.

  // Let's define the result as the count of the k-th most common word.
  // If k=0, means no words are considered, so the count threshold is 0 (or some sentinel).
  // If num_distinct_words = 0, then no words, so 0.

  // If k >= num_distinct_words, then all words are "most common", and the threshold is the minimum count among them.
  // If k < num_distinct_words, the threshold is the k-th largest count.

  // This function will return the k-th largest element in the word_counts array.
  // If k is 0, it means no words are selected, so the threshold could be 0.
  // If num_distinct_words == 0, it should return 0.
  // If k > num_distinct_words, it should return the minimum count in the array (as all words are in top-k).

  // To simplify, let's define "count the most common words" as:
  // "Return the count that separates the top K words from the rest."
  // This implies finding the K-th largest value in the `word_counts` array.
  // If there are ties, all words with that count or higher are included.
  // If k is 0, return 0 (no words selected).
  // If num_distinct_words is 0, return 0.
  // If k >= num_distinct_words, return the smallest count in the array (all words are in top-k).

  // Let's implement a simplified version: find the K-th largest count.
  // This requires sorting or a selection algorithm (like quickselect).
  // For Frama-C, a simple selection sort approach for finding k-th largest is more verifiable than quickselect.

  // The problem asks to "count the most common words", which is ambiguous.
  // A common interpretation for "count" is to return the minimum frequency among the top K words.
  // For example, if counts are [5, 3, 3, 2, 1] and K=2, top 2 are 5,3. So result is 3.
  // If K=3, top 3 are 5,3,3. So result is 3.
  // If K=4, top 4 are 5,3,3,2. So result is 2.

  // Let's define the function to return the K-th largest count.
  // If K is 0, no words are selected, so 0.
  // If num_distinct_words is 0, no words exist, so 0.
  // If K >= num_distinct_words, we return the smallest count in the array.
  // Otherwise, we find the K-th largest.

  // This requires a selection algorithm. For simplicity and verifiability,
  // we will find the K-th largest element using a selection sort-like approach.
  // This will modify a copy of the array internally.

  // To avoid modifying the input array, we would need to pass a mutable copy or
  // define a pure function that conceptually sorts.
  // For a pure function, we can use an axiomatic approach for sorted arrays.

  // Let's refine the return value:
  // Return the count threshold. All words with frequency >= this threshold are "most common".
  // If k = 0, return 0 (no words selected).
  // If num_distinct_words = 0, return 0.
  // Otherwise, find the k-th smallest element in the sorted DESCENDING list of counts.
  // Example: counts = [10, 20, 5, 15], num_distinct_words = 4
  // Sorted Desc: [20, 15, 10, 5]
  // if k=1, result = 20 (1st largest)
  // if k=2, result = 15 (2nd largest)
  // if k=3, result = 10 (3rd largest)
  // if k=4, result = 5 (4th largest)
  // if k > 4, result = 5 (all words are "most common", so the threshold is the lowest count among them)

  // This requires a selection algorithm. We will implement a simplified selection sort to find the k-th element.
  // This implies modifying the array. Since the input array `word_counts` is `const`,
  // we cannot modify it. We must therefore make a local copy.

  // The problem is about "counting the most common words". This could mean:
  // 1. Return the threshold frequency.
  // 2. Return the number of words that meet this threshold.

  // Let's assume interpretation 1: Return the frequency threshold.
  // We need to internally sort a copy of the array.

  // We need to define `sorted_descending` property for an array.
  logic boolean is_sorted_descending(int *arr, integer start, integer end);
  axiom is_sorted_descending_def{L}(int *arr, integer start, integer end) =
    is_sorted_descending(arr, start, end) <==>
      (\forall integer i; start <= i < end ==> arr[i] >= arr[i+1]);

  // Helper for sorting conceptually.
  // This is complex to do purely in ACSL.
  // A more practical approach for verifiability is to implement a simple selection sort
  // on a local copy of the array.

  // This function returns the K-th largest frequency.
  // If num_distinct_words is 0 or k is 0, result is 0.
  // If k >= num_distinct_words, result is the minimum frequency in the array.
  // Otherwise, it's the k-th largest frequency.
  // To avoid modifying the input array, we will create a temporary array for sorting.

  behavior zero_words:
    requires num_distinct_words == 0;
    assigns \nothing;
    ensures \result == 0;

  behavior zero_k:
    requires k == 0;
    assigns \nothing;
    ensures \result == 0;

  behavior all_words_top_k:
    requires num_distinct_words > 0;
    requires k >= num_distinct_words;
    assigns \nothing;
    ensures \result == \min(integer i; 0 <= i < num_distinct_words; word_counts[i]);

  behavior specific_k:
    requires num_distinct_words > 0;
    requires k > 0;
    requires k < num_distinct_words;
    assigns \nothing;
    // This requires specifying the k-th largest element.
    // This is hard to specify without a concept of sorting.
    // Let's use a simpler predicate based on the algorithm's outcome.
    // The algorithm will find the k-th largest element.
    // Let's assume a simplified problem: find the max of the first K elements.
    // No, "most common words" implies sorting.

    // Let's define the post-condition for the k-th largest element.
    // This uses a conceptual sorted array.
    // Let `sorted_counts` be the `word_counts` array sorted in descending order.
    // The result should be `sorted_counts[k-1]`.
    // This is very difficult to express directly in ACSL without
    // a full axiomatic theory of sorting.

    // Re-interpreting the problem for verifiability:
    // "Count the most common words" could mean: return a frequency `F` such that
    // at least `k` words have frequency `>= F`, and fewer than `k` words have frequency `> F`.
    // This is the definition of the k-th largest element.

    // Let's simplify the problem to "Find the K-th largest element in an array".
    // This needs a temporary mutable array.

    // The function `get_kth_largest_frequency` will return the k-th largest frequency.
    // To do this, we sort a copy of the array and return the element at index k-1.
    // We must ensure the `word_counts` array remains unchanged.

    // Let's define the full behavior.
    requires num_distinct_words >= 0;
    requires k >= 0;
    requires \valid_read(word_counts + (0..num_distinct_words - 1));
    // Max value of integer to avoid overflow for counts.
    requires \forall integer i; 0 <= i < num_distinct_words ==> word_counts[i] <= INT_MAX;

    assigns \nothing;

    ensures (num_distinct_words == 0 || k == 0) ==> \result == 0;
    ensures (num_distinct_words > 0 && k > 0);
    ensures (num_distinct_words > 0 && k >= num_distinct_words) ==> \result == \min(integer i; 0 <= i < num_distinct_words; word_counts[i]);
    // The most complex part: specifying the k-th largest element.
    // This requires a selection property.
    // Let R be the result.
    // (\count(integer i; 0 <= i < num_distinct_words; word_counts[i] >= R) >= k) &&
    // (\count(integer i; 0 <= i < num_distinct_words; word_counts[i] > R) < k)
    // This is the standard definition of the k-th largest element.
    // `\count` is available in ACSL.
    ensures (num_distinct_words > 0 && k > 0 && k < num_distinct_words) ==>
        (\count(integer i; 0 <= i < num_distinct_words; word_counts[i] >= \result) >= k &&
         \count(integer i; 0 <= i < num_distinct_words; word_counts[i] > \result) < k);
*/
int get_kth_largest_frequency(const int *word_counts, int num_distinct_words, int k) {
    // Rule I.2: Use int for booleans. Not directly applicable here.

    if (num_distinct_words == 0 || k == 0) {
        return 0;
    }

    // Create a mutable copy of the word_counts array.
    // This requires a fixed-size array or dynamic allocation.
    // For Frama-C, fixed-size arrays are easier to verify.
    // We need to assume a maximum size for `num_distinct_words`.
    // Let's assume a reasonable max size for verification purposes.
    // If we assume a max size, we must pass it in the requires clause.
    // For general solution, dynamic allocation `malloc` would be used, but
    // `malloc` is not allowed per Rule I.1.
    // So, we must work within the constraints.
    // The only way to have a mutable array is to pass it as an argument,
    // or assume a fixed maximum size for the array.
    // Let's assume `num_distinct_words` is always small enough for a VLA (though VLA are C99).
    // Or, for simplicity, use a static max size.

    // Let's assume `num_distinct_words` will not exceed a pre-defined maximum, e.g., 1000.
    // This is a common limitation for fully static verification without dynamic memory.
    // For this example, let's assume `num_distinct_words` is small enough for stack.
    // If it's a very large number, this approach won't work.

    // To avoid issues with VLAs and to stay within common Frama-C patterns,
    // we can implement a selection algorithm that does not require a full copy
    // if the problem implies finding the k-th element in the original array.
    // However, the problem statement says `const int *word_counts`, so we cannot modify it.

    // Given the constraints, the most verifiable approach for a `const` input
    // is to assume a small `num_distinct_words` and declare a VLA, or
    // to change the problem to allow modification of the input array.
    // Let's proceed with the VLA approach, acknowledging it's C99 and not C89.
    // Frama-C often supports VLAs.

    /*@
      // This ensures the VLA allocation is valid.
      // We need to ensure that `num_distinct_words` is not excessively large
      // to prevent stack overflow, which is a runtime error.
      // For verification, we add a practical limit.
      requires num_distinct_words <= 10000; // Example limit
    */
    int temp_counts[num_distinct_words];

    /*@
      loop invariant 0 <= i <= num_distinct_words;
      loop invariant \forall integer j; 0 <= j < i ==> temp_counts[j] == word_counts[j];
      loop assigns i, temp_counts[0..num_distinct_words-1];
      loop variant num_distinct_words - i;
    */
    for (int i = 0; i < num_distinct_words; i++) {
        temp_counts[i] = word_counts[i];
    }

    // Now, perform selection sort to find the k-th largest element.
    // We only need to sort up to the k-th element.
    // The k-th largest element will be at index k-1 after sorting in descending order.

    /*@
      loop invariant 0 <= i <= num_distinct_words;
      // Elements temp_counts[0...i-1] contain the i largest elements, sorted.
      loop invariant \forall integer x; 0 <= x < i ==>
          (\forall integer y; x < y < num_distinct_words ==> temp_counts[x] >= temp_counts[y]);
      // The elements temp_counts[0...i-1] are the largest i elements from the original array.
      // This is a strong invariant, hard to prove.
      // A simpler invariant: After `i` iterations, `temp_counts[i]` holds the `i`-th largest value.
      // No, selection sort places the i-th largest into `temp_counts[i-1]`.
      loop invariant 0 <= i <= num_distinct_words;
      loop invariant \forall integer x; 0 <= x < i ==>
          (\forall integer y; i <= y < num_distinct_words ==> temp_counts[x] >= temp_counts[y]); // elements 0..i-1 are greater than or equal to elements i..num_distinct_words-1
      loop invariant \forall integer x, y; 0 <= x < y < i ==> temp_counts[x] >= temp_counts[y]; // elements 0..i-1 are sorted descendingly

      loop assigns i, temp_counts[0..num_distinct_words-1];
      loop variant num_distinct_words - i;
    */
    for (int i = 0; i < num_distinct_words; i++) {
        /*@
          loop invariant i <= j <= num_distinct_words;
          loop invariant i <= max_idx < num_distinct_words;
          // max_idx holds the index of the maximum element in temp_counts[i..j-1].
          loop invariant \forall integer l; i <= l < j ==> temp_counts[l] <= temp_counts[max_idx];
          loop assigns j, max_idx;
          loop variant num_distinct_words - j;
        */
        int max_idx = i;
        for (int j = i + 1; j < num_distinct_words; j++) {
            if (temp_counts[j] > temp_counts[max_idx]) {
                max_idx = j;
            }
        }

        // Swap temp_counts[i] and temp_counts[max_idx]
        if (max_idx != i) {
            int temp = temp_counts[i];
            temp_counts[i] = temp_counts[max_idx];
            temp_counts[max_idx] = temp;
        }

        // Optimization: if we have found the k-th largest element, we can stop.
        // The k-th largest element (1-indexed) will be at index k-1 (0-indexed) after sorting.
        // If k >= num_distinct_words, we need the smallest element, which will be at the end.
        // If k < num_distinct_words, we only need to sort up to index k-1.
        /*@
          // This check ensures we stop early if we have found the k-th largest.
          // If k is small, we don't need to sort the whole array.
          // This must be `i == k - 1` because `i` is 0-indexed.
          // If `k >= num_distinct_words`, we must find the smallest, which is the last element.
          // So we must sort the whole array to guarantee the smallest is at the end.
          // Or, we find `k` elements.
        */
        if (k <= num_distinct_words && i == k - 1) {
             return temp_counts[k - 1]; // Found the k-th largest
        }
    }

    // If k >= num_distinct_words, we need the smallest element, which is the last one after full descending sort.
    // Or if num_distinct_words > 0, and k is also > 0, but we didn't return early.
    // This happens when k >= num_distinct_words. In this case, the result is the minimum frequency.
    // After sorting in descending order, the minimum frequency is at temp_counts[num_distinct_words - 1].
    if (num_distinct_words > 0) {
        return temp_counts[num_distinct_words - 1];
    }

    return 0; // Should not be reached if initial checks are handled. Redundant for safety.
}
