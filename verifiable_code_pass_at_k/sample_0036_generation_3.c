// Task ID: 36
// Generation: 3

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay not applicable here.

  // Axiomatic block for recursive logic (Rule II.1).
  // Not strictly needed for this simple problem, but good practice for more complex ones.
  // Demonstrates how to define a logic function.
  axiomatic DigitExtraction {
    logic integer get_nth_digit_recursive(integer num, integer den, integer n)
      reads num, den, n;

    // Base case: 0th digit
    axiom nth_digit_base:
      \forall integer num, den;
        0 <= num < den && den > 0 ==> get_nth_digit_recursive(num, den, 0) == (num * 10) / den;

    // Recursive step
    axiom nth_digit_rec:
      \forall integer num, den, n;
        0 <= num < den && den > 0 && n > 0 ==>
          get_nth_digit_recursive(num, den, n) == get_nth_digit_recursive((num * 10) % den, den, n - 1);

    // Rule II.2: Helper axioms (lemmas). Example: A digit is always between 0 and 9.
    axiom digit_range:
      \forall integer num, den, n;
        0 <= num < den && den > 0 && n >= 0 ==>
          0 <= get_nth_digit_recursive(num, den, n) <= 9;
  }
*/

/*@
  requires numerator >= 0;
  requires denominator > 0;
  // Proper fraction: numerator < denominator.
  // This also implies numerator is not negative if denominator is positive.
  requires numerator < denominator;
  requires n >= 0;

  // Rule II.5: Prevent overflow.
  // The value 'current_numerator' can grow up to (denominator - 1) * 10.
  // If we multiply by 10 'n' times, it can be numerator * 10^n.
  // We need to ensure that numerator * 10^n does not overflow 'int'.
  // A conservative bound: (denominator - 1) * 10 is the max value *before* taking modulo.
  // The intermediate `current_numerator * 10` must not overflow.
  // Max value of `current_numerator` is `denominator - 1`. So, `(denominator - 1) * 10` must fit.
  // A simpler, but often sufficient, requires for typical values:
  // Frama-C's INT_MAX is 2147483647.
  // For `(denominator - 1) * 10` to not overflow, `denominator - 1` must be less than `INT_MAX / 10`.
  // So, `denominator <= INT_MAX / 10 + 1`.
  requires denominator <= 214748364; // INT_MAX / 10 is 214748364.
  // Additionally, n could be large, leading to many multiplications by 10.
  // However, since we take modulo in each step, the `current_numerator` will always be `< denominator`.
  // So, the overflow check only needs to consider `denominator * 10`.

  assigns \nothing;

  // Rule II.3: Ensures clause for boolean-like functions (though this returns a digit).
  // This ensures the result is precisely the nth digit as defined by the axiomatic function.
  // Rule III.2: No parentheses around if-then-else. Not applicable here.
  // Rule III.1: No C-style ternary in ACSL. Not applicable here.
  ensures \result == get_nth_digit_recursive(numerator, denominator, n);
*/
int get_nth_decimal_digit(int numerator, int denominator, int n) {
    int current_numerator = numerator;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant 0 <= current_numerator < denominator;
      // This invariant links current_numerator to the recursive definition.
      // After 'i' steps, current_numerator is equivalent to (numerator * 10^i) % denominator.
      // This is exactly the numerator part needed for the (n-i)-th digit calculation.
      loop invariant current_numerator == \at(numerator, Pre) *
                                         (if i == 0 then 1 else (\pow(10, i) % \at(denominator, Pre))) % \at(denominator, Pre);
      loop invariant (get_nth_digit_recursive(\at(numerator, Pre), \at(denominator, Pre), n) ==
                      get_nth_digit_recursive(current_numerator, \at(denominator, Pre), n - i));
      loop assigns i, current_numerator;
      // Rule II.4: Loop variant for termination.
      loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        // Rule II.5: Prevent overflow for current_numerator * 10.
        // We know current_numerator < denominator, and denominator <= INT_MAX / 10.
        // So current_numerator * 10 < denominator * 10 <= (INT_MAX / 10) * 10 = INT_MAX.
        current_numerator = current_numerator * 10;
        current_numerator = current_numerator % denominator;
    }

    // Rule II.5: Prevent overflow for current_numerator * 10. Same logic as above.
    return (current_numerator * 10) / denominator;
}
