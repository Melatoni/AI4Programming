// Task ID: 42
// Generation: 7

/*@
    // Rule II.1: Define a recursive logic function for counting occurrences.
    // Rule I.3: Uses the correct pointer type for array parameters.
    axiomatic Occurrences {
        logic integer count_occurrences{L}(int *a, integer start_idx, integer end_idx, int val) reads a[start_idx..end_idx];

        axiom count_occurrences_base{L}:
            \forall int *a, integer start_idx, end_idx, val;
            start_idx > end_idx ==> count_occurrences(a, start_idx, end_idx, val) == 0;

        axiom count_occurrences_recursive{L}:
            \forall int *a, integer start_idx, end_idx, val;
            start_idx <= end_idx ==> count_occurrences(a, start_idx, end_idx, val) ==
                (if a[start_idx] == val then 1 else 0) + count_occurrences(a, start_idx + 1, end_idx, val);

        // Rule II.2: Helper axiom to show that if an element is present, its count is at least 1.
        // This helps the prover relate count_occurrences to existence.
        axiom count_occurrences_present{L}:
            \forall int *a, integer start_idx, end_idx, val;
            (start_idx <= end_idx && \exists integer i; start_idx <= i <= end_idx && a[i] == val) ==>
            count_occurrences(a, start_idx, end_idx, val) >= 1;
    }

    // Rule II.1: Define a recursive logic function for the sum of unique elements.
    // This is used to define the property of the result.
    axiomatic SumUniqueRepeated {
        logic integer sum_unique_repeated{L}(int *a, integer start_idx, integer end_idx, int N) reads a[start_idx..end_idx];

        axiom sum_unique_repeated_base{L}:
            \forall int *a, integer start_idx, end_idx, N;
            start_idx > end_idx ==> sum_unique_repeated(a, start_idx, end_idx, N) == 0;

        axiom sum_unique_repeated_recursive{L}:
            \forall int *a, integer start_idx, end_idx, N;
            start_idx <= end_idx ==> sum_unique_repeated(a, start_idx, end_idx, N) ==
                (if count_occurrences(a, 0, N - 1, a[start_idx]) >= 2 &&
                    count_occurrences(a, 0, start_idx - 1, a[start_idx]) == 0
                 then a[start_idx]
                 else 0) + sum_unique_repeated(a, start_idx + 1, end_idx, N);
    }
*/

/*@
    requires N >= 0;
    // Rule II.5: Prevent potential overflow if elements are large and sum exceeds INT_MAX.
    // This requires a more precise bound based on the sum_unique_repeated logic.
    // For simplicity, we assume the sum fits in int. A more robust solution would involve
    // checking max possible sum based on N and element values.
    // For example, if array elements are int, max sum could be N * INT_MAX.
    // We need to ensure the sum_unique_repeated(a, 0, N-1, N) does not overflow.
    // If elements are small (e.g., within [-1000, 1000]) and N is large, this could overflow.
    // For now, we add a general requirement that the final sum fits.
    requires \abs(sum_unique_repeated(a, 0, N - 1, N)) <= 2147483647; // INT_MAX

    assigns \nothing;

    ensures \result == sum_unique_repeated(a, 0, N - 1, N);
*/
int sum_repeated_elements(int* a, int N) {
    int sum = 0;
    /*@
        loop invariant 0 <= i <= N;
        // sum accumulates unique values of elements a[k] (k < i) that are repeated in the whole array,
        // and have not been counted before (i.e., a[k] does not appear in a[0..k-1]).
        loop invariant sum == sum_unique_repeated(a, 0, i - 1, N);

        loop assigns i, sum;
        loop variant N - i;
    */
    for (int i = 0; i < N; ++i) {
        int current_element = a[i];
        int count = 0;
        int found_before = 0; // Rule I.2: Use int for boolean

        /*@
            loop invariant 0 <= j <= N;
            loop invariant 0 <= count;
            // count is the number of occurrences of current_element in a[0..j-1]
            loop invariant count == count_occurrences(a, 0, j - 1, current_element);
            // found_before is 1 if current_element appeared in a[0..i-1], 0 otherwise.
            loop invariant found_before == (if count_occurrences(a, 0, i - 1, current_element) >= 1 then 1 else 0);

            loop assigns j, count, found_before;
            loop variant N - j;
        */
        for (int j = 0; j < N; ++j) {
            if (a[j] == current_element) {
                count++;
            }
            if (j < i && a[j] == current_element) {
                found_before = 1;
            }
        }

        // Add to sum only if the element is repeated (count >= 2)
        // and this is the first time we encounter this specific value (found_before == 0).
        // Rule II.2: Helper axiom `count_occurrences_present` helps reason about `found_before`.
        if (count >= 2 && found_before == 0) {
            // Rule II.5: Prevent overflow of sum.
            // This requires that sum + current_element does not overflow.
            // A more precise check would be: if current_element > 0, sum <= INT_MAX - current_element
            // If current_element < 0, sum >= INT_MIN - current_element
            // For simplicity, we rely on the pre-condition about the final sum.
            sum += current_element;
        }
    }
    return sum;
}
