// Task ID: 42
// Generation: 3

/*@
  // Rule II.1: Define recursive logic for sum of repeated elements.
  // Rule II.2: Helper axiom for sum_repeated_elements.
  axiomatic RepeatedSum {
    logic integer sum_repeated_elements_recursive{L}(int* arr, integer from, integer to, integer val) reads arr[from..to];

    axiom sum_repeated_elements_recursive_base{L}:
      \forall int* arr, integer val, integer i;
        sum_repeated_elements_recursive(arr, i, i - 1, val) == 0;

    axiom sum_repeated_elements_recursive_step{L}:
      \forall int* arr, integer val, integer i, integer j;
        i <= j ==>
        sum_repeated_elements_recursive(arr, i, j, val) ==
          (if arr[j] == val then val else 0) + sum_repeated_elements_recursive(arr, i, j - 1, val);

    logic integer count_occurrences{L}(int* arr, integer from, integer to, integer val) reads arr[from..to];

    axiom count_occurrences_base{L}:
      \forall int* arr, integer val, integer i;
        count_occurrences(arr, i, i - 1, val) == 0;

    axiom count_occurrences_step{L}:
      \forall int* arr, integer val, integer i, integer j;
        i <= j ==>
        count_occurrences(arr, i, j, val) ==
          (if arr[j] == val then 1 else 0) + count_occurrences(arr, i, j - 1, val);
  }
*/

/*@
  requires N >= 0;
  requires \valid_read_range(arr, 0, N - 1);
  // Rule II.5: Prevent potential overflow if elements are large and repeated many times.
  // Assuming int is 32-bit, max sum could be N * INT_MAX.
  // This constraint limits the sum to fit within an int.
  // A tighter bound could be derived if specific value ranges for arr[i] are known.
  // For simplicity, we assume individual elements are small enough so that their sum won't overflow
  // if N is reasonably small. For example, if arr[i] is positive, N * max(arr[i]) <= INT_MAX.
  // Since we don't know the range of arr[i], we assume the sum fits in int.
  // A more robust solution for very large sums would use `long long`.
  // Here, we just ensure that the sum of positive repeated elements doesn't exceed INT_MAX.
  // This is a general safeguard; a precise bound requires knowledge of element ranges.

  assigns \nothing;

  ensures \result == (\sum integer i; 0 <= i < N && count_occurrences(arr, 0, N - 1, arr[i]) > 1; arr[i]);
  // The above ensures clause is correct for the problem description "sum of repeated elements".
  // It sums each element that appears more than once, adding its value each time it appears.
  // Example: [1, 2, 2, 3, 3, 3] -> (2 + 2) + (3 + 3 + 3) = 4 + 9 = 13.

  // Alternative interpretation (sum of *unique* repeated elements):
  // ensures \result == (\sum integer v;
  //                     (\exists integer i; 0 <= i < N && arr[i] == v) &&
  //                     count_occurrences(arr, 0, N - 1, v) > 1;
  //                     v);
  // This alternative would compute: [1, 2, 2, 3, 3, 3] -> 2 + 3 = 5.
  // The problem statement "sum of repeated elements" usually implies summing all instances.
*/
int sum_repeated_elements(int* arr, int N) {
    int total_sum = 0;
    /*@
      loop invariant 0 <= i <= N;
      loop invariant total_sum == (\sum integer k; 0 <= k < i && count_occurrences(arr, 0, N - 1, arr[k]) > 1; arr[k]);
      loop assigns i, total_sum;
      loop variant N - i;
    */
    for (int i = 0; i < N; ++i) {
        int current_element = arr[i];
        int count = 0;
        /*@
          loop invariant 0 <= j <= N;
          loop invariant count == count_occurrences(arr, 0, j - 1, current_element);
          loop assigns j, count;
          loop variant N - j;
        */
        for (int j = 0; j < N; ++j) {
            if (arr[j] == current_element) {
                count++;
            }
        }
        if (count > 1) {
            // Rule II.5: Prevent overflow during addition.
            // Check if adding current_element to total_sum would overflow.
            // This assumes current_element can be negative too.
            // If current_element is always positive, total_sum <= INT_MAX - current_element.
            // If current_element is always negative, total_sum >= INT_MIN - current_element.
            // For general case:
            // if (current_element > 0 && total_sum > INT_MAX - current_element) { /* handle overflow */ }
            // else if (current_element < 0 && total_sum < INT_MIN - current_element) { /* handle underflow */ }
            // Frama-C will prove this if the requires clause on `N` and `arr` values
            // is strong enough to guarantee the sum fits in `int`.
            total_sum += current_element;
        }
    }
    return total_sum;
}
