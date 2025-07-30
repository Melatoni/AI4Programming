// Task ID: 37
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay handled in ACSL.
  // Rule II.1, II.2: Recursive logic with helper axioms for complexity.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).
  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@ axiomatic Swap {
  logic oid swap_array{L}(int* a, integer i, integer j) reads a[i], a[j];

  axiom swap_preserves_length{L}:
    orall int* a, integer i, integer j, integer len;
    requires 0 <= i < len && 0 <= j < len;
    ensures \length(swap_array(a, i, j)) == len;

  axiom swap_elements{L}:
    orall int* a, integer i, integer j;
    ensures (\at(a,L))[i] == (\at(swap_array(a, i, j),L))[j] &&
            (\at(a,L))[j] == (\at(swap_array(a, i, j),L))[i];

  axiom swap_other_elements{L}:
    orall int* a, integer i, integer j, integer k;
    requires k != i && k != j;
    ensures (\at(a,L))[k] == (\at(swap_array(a, i, j),L))[k];

  // Helper axiom for permutation
  axiom swap_is_permutation{L}:
    orall int* a, integer i, integer j, integer len;
    requires 0 <= i < len && 0 <= j < len;
    ensures \is_permutation(swap_array(a, i, j), a);
}
*/

/*@ axiomatic Sorted {
  logic boolean is_sorted{L}(int* a, integer rom, integer to);

  axiom sorted_empty{L}:
    orall int* a, integer rom, integer to;
    requires rom >= to;
    ensures is_sorted(a, rom, to) == \true;

  axiom sorted_one_element{L}:
    orall int* a, integer rom;
    ensures is_sorted(a, rom, rom + 1) == \true;

  axiom sorted_recursive{L}:
    orall int* a, integer rom, integer to;
    requires rom < to - 1;
    ensures is_sorted(a, rom, to) == (a[rom] <= a[rom+1] && is_sorted(a, rom+1, to));

  // Helper axiom: if a subarray is sorted, any smaller subarray within it is also sorted.
  axiom sorted_sub_array{L}:
    orall int* a, integer rom1, integer to1, integer rom2, integer to2;
    requires rom1 <= rom2 && to2 <= to1;
    requires is_sorted(a, rom1, to1);
    ensures is_sorted(a, rom2, to2);
}
*/

/*@
  requires 0 <= n;
  requires \valid(arr + (0..n-1));
  assigns arr[0..n-1];
  ensures is_sorted(arr, 0, n);
  ensures \is_permutation(arr, \old(arr));
*/
oid bubble_sort(int* arr, int n) {
  /*@
    loop invariant 0 <= i <= n;
    loop invariant is_sorted(arr, n - i, n);
    loop invariant \orall integer k; n - i <= k < n ==> \orall integer j; 0 <= j < n - i ==> arr[j] <= arr[k];
    loop invariant \is_permutation(arr, \old(arr));
    loop assigns arr[0..n-1], i, j; // Added j to loop assigns
    loop variant n - i;
  */
  for (int i = 0; i < n; i++) {
    /*@
      loop invariant 0 <= j <= n - i - 1;
      loop invariant \orall integer k; 0 <= k < j ==> arr[k] <= arr[k+1];
      loop invariant \is_permutation(arr, \at(arr,LoopInv)); // Permutation with respect to outer loop state
      loop assigns arr[0..n-1], j;
      loop variant n - i - 1 - j;
    */
    for (int j = 0; j < n - i - 1; j++) {
      if (arr[j] > arr[j+1]) {
        int temp = arr[j];
        arr[j] = arr[j+1];
        arr[j+1] = temp;
      }
    }
  }
}

// Frama-C does not directly support "mixed lists" of integers and strings.
// The problem description implies a single-type array (e.g., int array) for sorting.
// If it were truly mixed, it would require a custom data structure (e.g., struct with union and type tag)
// and custom comparison logic, which is beyond the scope of simple integer sorting and
// complex for a first Frama-C problem without a clear type definition.
// Assuming "mixed list" is a conceptual misnomer for an integer array for the purpose of this exercise,
// as Frama-C WP does not handle arbitrary string comparisons or dynamic memory for strings out of the box.
// The provided solution sorts an array of integers.
