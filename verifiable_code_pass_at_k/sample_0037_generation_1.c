// Task ID: 37
// Generation: 1

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay - not applicable here as we sort an int array.

  // Rule II.1: Recursive logic for complexity - not directly applicable for a simple sort.
  // Rule II.2: Helper axioms - not directly applicable.
  // Rule II.3: ensures clause for Boolean-like functions - not applicable as this is a void function.
  // Rule II.5: Prevent Runtime Errors (RTE) - check array bounds and input validity.

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct Range Syntax.
  // Rule III.4: No stray semicolons.

  requires \valid(arr + (0..size-1));
  requires size >= 0;
  assigns arr[0..size-1];

  // Post-condition: The array is sorted in non-decreasing order.
  ensures \forall integer i; 0 <= i < size - 1 ==> arr[i] <= arr[i+1];
  // Post-condition: The array is a permutation of the original array.
  ensures \forall integer x;
    (\numof(integer i; 0 <= i < size && arr[i] == x)) ==
    (\numof(integer j; 0 <= j < size && \old(arr[j]) == x));
*/
void sort_int_array(int arr[], int size) {
    /*@
      loop invariant 0 <= i <= size;
      loop invariant \forall integer k; 0 <= k < i ==> \forall integer l; i <= l < size ==> arr[k] <= arr[l];
      loop invariant \forall integer k; 0 <= k < i-1 ==> arr[k] <= arr[k+1];
      loop invariant \forall integer x;
        (\numof(integer m; 0 <= m < size && arr[m] == x)) ==
        (\numof(integer n; 0 <= n < size && \at(arr[n], Pre) == x));
      loop assigns i, arr[0..size-1];
      loop variant size - i;
    */
    for (int i = 0; i < size - 1; i++) {
        /*@
          loop invariant i <= j <= size;
          loop invariant \forall integer k; i <= k < j ==> arr[i] <= arr[k];
          loop invariant \forall integer k; i <= k < j ==> \forall integer l; j <= l < size ==> arr[k] <= arr[l]; // This helps show the current min is correctly placed
          loop invariant \forall integer k; i <= k < j ==> arr[k] >= \at(arr[i], LoopCurrent); // Elements before current j are already processed and are not smaller than arr[i]
          loop invariant \forall integer k; i <= k < j ==> arr[k] >= arr[i]; // All elements from i to j-1 are >= arr[i]
          loop invariant \forall integer x;
            (\numof(integer m; 0 <= m < size && arr[m] == x)) ==
            (\numof(integer n; 0 <= n < size && \at(arr[n], Pre) == x));
          loop assigns j, arr[0..size-1];
          loop variant size - j;
        */
        for (int j = i + 1; j < size; j++) {
            if (arr[i] > arr[j]) {
                int temp = arr[i];
                arr[i] = arr[j];
                arr[j] = temp;
            }
        }
    }
}
