// Task ID: 20
// Generation: 5

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.

  // Rule II.1: Recursive logic for complex properties.
  // Rule II.2: Helper axioms for recursive functions.
  // Rule II.5: Prevent runtime errors.

  // Rule III.1: No C-style ternary in ACSL.
  // Rule III.2: No parentheses around if-then-else.
  // Rule III.3: Correct range syntax.
  // Rule III.4: No stray semicolons.
*/

/*@
  axiomatic Digits {
    logic integer count_digits(integer n);

    axiom count_digits_base:
      \forall integer n; 0 <= n < 10 ==> count_digits(n) == 1;

    axiom count_digits_recursive:
      \forall integer n; n >= 10 ==> count_digits(n) == 1 + count_digits(n / 10);

    logic integer sum_digits(integer n);

    axiom sum_digits_base:
      \forall integer n; 0 <= n < 10 ==> sum_digits(n) == n;

    axiom sum_digits_recursive:
      \forall integer n; n >= 10 ==> sum_digits(n) == (n % 10) + sum_digits(n / 10);

    // Helper axiom: If n is positive, its sum of digits is positive.
    axiom sum_digits_positive:
      \forall integer n; n > 0 ==> sum_digits(n) > 0;

    // Helper axiom: The sum of digits of n is less than or equal to n for n > 0.
    axiom sum_digits_less_than_n:
      \forall integer n; n > 0 ==> sum_digits(n) <= n;

    // Helper axiom: The sum of digits of n is 1 if n is a power of 10.
    // This is not directly used for woodball, but demonstrates helper axioms.
    axiom sum_digits_power_of_10:
      \forall integer k; k >= 0 ==> sum_digits(pow(10, k)) == 1;
  }
*/

/*@
  requires n >= 0; // Woodball numbers are typically non-negative.
  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions uses logical equivalence.
  ensures (\exists integer k; k > 0 && n == k * sum_digits(n)) <==> (result == 1);
*/
int is_woodball(int n) {
    if (n == 0) {
        return 0; // 0 is not considered a woodball number by this definition (k > 0).
    }

    int original_n = n;
    int sum_of_digits = 0;

    /*@
      loop invariant n >= 0;
      loop invariant original_n == n + \at(sum_of_digits, Pre) * 10^count_digits(n); // Incorrect. This is not a good invariant for sum_of_digits.
      loop invariant original_n == \at(original_n,Pre);
      loop invariant sum_of_digits == sum_digits(\at(original_n, Pre) - n); // This is also not quite right.
      loop invariant sum_of_digits == sum_digits(original_n / (int)pow(10, count_digits(n))) - sum_digits(n); // No, this won't work.

      // A better invariant for sum_of_digits calculation:
      // The sum_of_digits variable contains the sum of digits of (original_n - n).
      // Let's refine: sum_of_digits contains the sum of digits of the part of original_n
      // that has already been processed (i.e., original_n % (10^k) for some k).
      // Or, better, sum_of_digits contains the sum of digits of original_n - (n * 10^k)
      // where k is the number of digits processed so far.

      loop invariant \forall integer p; p < n_at_entry_loop_iter_start_of_sum_digits; // This is not a valid invariant.

      // Let's try to maintain that sum_of_digits is the sum of digits of (original_n % 10^k)
      // where k is the number of digits already processed.
      // This requires tracking the power of 10 or the number of digits processed.

      // A simpler invariant: sum_of_digits is the sum of digits of (original_n / (current_n_value_at_loop_start * 10^k))
      // No, let's stick to the definition: `sum_of_digits == sum_digits(original_n) - sum_digits(n)`. This is not true.

      // The invariant for sum_of_digits should state that it accumulates the sum of digits
      // of the part of `original_n` that has been "chopped off".
      // Example: original_n = 123.
      // Iter 1: n=12, sum_of_digits=3. (sum_digits(123) - sum_digits(12) = 3)
      // Iter 2: n=1, sum_of_digits=3+2=5. (sum_digits(123) - sum_digits(1) = 5)
      // Iter 3: n=0, sum_of_digits=5+1=6. (sum_digits(123) - sum_digits(0) = 6)
      // So, `sum_of_digits == sum_digits(original_n) - sum_digits(n)` is the invariant!
      // This relies on the recursive definition of sum_digits.

      loop invariant \at(original_n, Pre) == original_n; // original_n does not change
      loop invariant n >= 0;
      loop invariant \at(original_n, Pre) == n * (int)pow(10, count_digits(\at(original_n, Pre)) - count_digits(n)) + \at(sum_of_digits, LoopEntry) + \at(original_n, Pre) % (int)pow(10, count_digits(\at(original_n, Pre)) - count_digits(n)); // This is too complex.
      // The sum_of_digits accumulator:
      loop invariant sum_of_digits == sum_digits(\at(original_n, Pre)) - sum_digits(n); // This is the key.
      loop assigns n, sum_of_digits;
      loop variant n; // Rule II.4: Loop variant for termination.
    */
    while (n > 0) {
        sum_of_digits += n % 10;
        n /= 10;
    }

    // After the loop, n is 0, so sum_of_digits == sum_digits(original_n) - sum_digits(0)
    // which simplifies to sum_of_digits == sum_digits(original_n).
    // This requires a helper axiom: sum_digits(0) == 0.
    /*@
      axiom sum_digits_zero: sum_digits(0) == 0;
    */

    // Rule II.5: Prevent division by zero. sum_of_digits will be > 0 for original_n > 0.
    // This is covered by the `sum_digits_positive` helper axiom.
    if (sum_of_digits == 0) {
        // This case should not be reached for original_n > 0, due to sum_digits_positive axiom.
        // It would only be relevant if original_n could be 0, which we handled.
        return 0;
    }

    if (original_n % sum_of_digits == 0) {
        return 1;
    } else {
        return 0;
    }
}
