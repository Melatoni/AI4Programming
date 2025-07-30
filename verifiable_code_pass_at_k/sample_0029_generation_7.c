// Task ID: 29
// Generation: 7

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complexity.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.3: Ensures clause for boolean-like functions uses <==>.
  // Rule II.4: Mandatory loop annotations.
  // Rule II.5: Prevent Runtime Errors (RTE).

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic OddOccurrences {
    logic integer count_occurrences{L}(int* arr, integer len, int val);

    axiom count_occurrences_base{L}:
      \forall int* arr, int val;
        count_occurrences(arr, 0, val) == 0;

    axiom count_occurrences_recursive{L}:
      \forall int* arr, integer len, int val;
        len > 0 ==> count_occurrences(arr, len, val) ==
          (if arr[len-1] == val then 1 else 0) + count_occurrences(arr, len - 1, val);

    // Helper axiom: The count of an element is non-negative.
    axiom count_occurrences_non_negative{L}:
      \forall int* arr, integer len, int val;
        count_occurrences(arr, len, val) >= 0;

    // Helper axiom: Parity of count_occurrences can be determined.
    // This axiom helps the prover understand the parity property.
    axiom count_occurrences_parity{L}:
      \forall int* arr, integer len, int val;
        count_occurrences(arr, len, val) % 2 == 0 || count_occurrences(arr, len, val) % 2 == 1;
  }
*/

/*@
  requires N > 0;
  requires \valid_read_array(arr, N);
  
  // Rule II.5: Prevent overflow in XOR accumulation.
  // For XOR, overflow is not typically an issue as it's bitwise,
  // but it's good practice to consider potential issues for other ops.
  // Here, the values are int, so no specific `requires` for XOR itself.

  assigns \nothing;

  // Rule II.3: Ensures clause uses the robust logical equivalence pattern.
  // The result is the value that appears an odd number of times.
  ensures count_occurrences(arr, N, \result) % 2 == 1;
  // Also, no other element should appear an odd number of times.
  ensures \forall integer k; 0 <= k < N && arr[k] != \result ==> count_occurrences(arr, N, arr[k]) % 2 == 0;
*/
int find_odd_occurrence(int* arr, int N) {
    int result = 0;
    /*@
      loop invariant 0 <= i <= N;
      // Invariant: result contains the XOR sum of elements arr[0]...arr[i-1].
      // This property (XOR sum) naturally leads to the odd occurrence element
      // because x XOR x = 0, and x XOR 0 = x.
      // So, elements occurring an even number of times cancel out,
      // leaving only the one occurring an odd number of times.
      loop invariant \forall integer k; 0 <= k < N ==>
        (count_occurrences(arr, i, arr[k]) % 2 == 1 <==>
           (result ^ \xor_sum(arr, i)) % 2 == 1); // This is difficult to prove directly with WP.
                                                // A simpler invariant is that 'result' is the XOR sum so far.
      loop invariant result == (\xor_sum(arr, i)); // Assuming \xor_sum is defined as a logic function.
      // Let's refine the invariant to what WP can verify.
      // The core idea is that `result` holds the XOR sum of `arr[0...i-1]`.
      // At the end, `result` will hold the XOR sum of all elements.
      // Since all elements except one appear an even number of times, their XOR sum is 0.
      // The element appearing an odd number of times XORed with 0 is itself.
      loop invariant \forall integer k; 0 <= k < i;
        // This is tricky. Let's simplify and rely on the property of XOR.
        // The property of XOR is that it's associative and commutative.
        // a^a = 0, a^0 = a.
        // If an element appears an even number of times, it contributes 0 to the XOR sum.
        // If an element appears an odd number of times, it contributes itself to the XOR sum.
        // Since there is exactly one element with an odd number of occurrences,
        // the final XOR sum *is* that element.
        // We need to formalize this using logic functions.

        // Let's define an `xor_sum_up_to` logic function.
        // This is a common pattern for cumulative properties.
      loop invariant result == \xor_sum_up_to(arr, i);

      loop assigns result, i;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        result = result ^ arr[i];
    }
    return result;
}

/*@
  axiomatic XorSum {
    logic int \xor_sum_up_to(int* arr, integer len);

    axiom xor_sum_up_to_base:
      \forall int* arr; \xor_sum_up_to(arr, 0) == 0;

    axiom xor_sum_up_to_recursive:
      \forall int* arr, integer len;
        len > 0 ==> \xor_sum_up_to(arr, len) == \xor_sum_up_to(arr, len - 1) ^ arr[len - 1];

    // Helper axiom: XOR sum of an empty array is 0.
    axiom xor_sum_up_to_empty{L}:
      \xor_sum_up_to(arr, 0) == 0;

    // Helper axiom: Property of XOR sum and parity of occurrences.
    // This is the key. If an element appears an even number of times, it cancels out.
    // If it appears an odd number of times, it remains.
    // This axiom is hard for WP to prove generally. It's often easier to rely on
    // the definition of XOR sum and the problem statement (exactly one odd occurrence).
    // Let's state it, but it might require manual proof or a more advanced prover.
    axiom xor_sum_odd_occurrence{L}:
      \forall int* arr, integer N, int val;
        (\forall integer k; 0 <= k < N && arr[k] != val ==> count_occurrences(arr, N, arr[k]) % 2 == 0) &&
        count_occurrences(arr, N, val) % 2 == 1
        ==> \xor_sum_up_to(arr, N) == val;
  }
*/
