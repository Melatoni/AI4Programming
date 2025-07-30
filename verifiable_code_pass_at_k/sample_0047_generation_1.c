// Task ID: 47
// Generation: 1

/*@
  // Axiomatic block to define factorial recursively.
  // Rule II.1: Recursive logic for complex properties.
  axiomatic Factorial {
    logic integer factorial(integer n);

    axiom factorial_base:
      factorial(0) == 1;

    axiom factorial_rec:
      \forall integer n; n > 0 ==> factorial(n) == n * factorial(n - 1);

    // Helper axioms for factorial properties.
    // Rule II.2: CRITICAL - Helper Axioms.
    // These help the prover deduce properties about factorial.
    // Factorial is always positive for n >= 0.
    axiom factorial_positive:
      \forall integer n; n >= 0 ==> factorial(n) > 0;

    // Factorial grows very quickly.
    // This helps reason about divisibility.
    axiom factorial_divisibility:
      \forall integer n, m; 0 <= m <= n ==> factorial(n) % factorial(m) == 0;

    // Last digit of factorial(n) for n >= 5 is 0.
    // This is crucial for the problem.
    axiom factorial_last_digit_zero:
      \forall integer n; n >= 5 ==> factorial(n) % 10 == 0;

    // Last digit of factorial(0) to factorial(4)
    axiom factorial_last_digit_0: factorial(0) % 10 == 1;
    axiom factorial_last_digit_1: factorial(1) % 10 == 1;
    axiom factorial_last_digit_2: factorial(2) % 10 == 2;
    axiom factorial_last_digit_3: factorial(3) % 10 == 6;
    axiom factorial_last_digit_4: factorial(4) % 10 == 4;
  }
*/

/*@
  // Axiomatic block for the last digit of n / m.
  // This is specific to the problem's interpretation of "last digit".
  // Rule II.1: Recursive logic for complex properties.
  axiomatic LastDigitOfQuotient {
    logic integer last_digit_quotient(integer num, integer den);

    // Define the last digit as (num / den) % 10.
    // Requires den to be non-zero and num divisible by den.
    axiom last_digit_quotient_def:
      \forall integer num, den; den != 0 && num % den == 0 ==>
        last_digit_quotient(num, den) == (num / den) % 10;
  }
*/

/*@
  requires a >= 0;
  requires b >= 0;
  // Constraint for 'a' to prevent overflow when calculating factorial(a)
  // for typical 32-bit int. Factorial(12) is 479,001,600. Factorial(13) overflows.
  // This is a practical limit for 'int' type.
  requires a <= 12;
  // Constraint for 'b' to prevent overflow when calculating factorial(b)
  requires b <= 12;

  // factorial(b) must be divisible by factorial(a).
  // This is true if a <= b, which is covered by the factorial_divisibility axiom.
  requires a <= b;

  assigns \nothing;

  // Rule II.3: Ensures clause using logical equivalence.
  // The result is the last digit of factorial(b) / factorial(a).
  ensures \result == last_digit_quotient(factorial(b), factorial(a));
*/
int find_last_digit_factorial_quotient(int a, int b) {
    // Since a and b are small (<= 12), we can compute factorials directly
    // and then the quotient.
    // The problem asks for the *last digit* of the quotient.

    int fact_a = 1;
    /*@
      loop invariant 0 <= i <= a;
      loop invariant fact_a == factorial(i);
      loop assigns i, fact_a;
      loop variant a - i;
    */
    for (int i = 0; i < a; ++i) {
        fact_a *= (i + 1);
    }

    int fact_b = 1;
    /*@
      loop invariant 0 <= i <= b;
      loop invariant fact_b == factorial(i);
      loop assigns i, fact_b;
      loop variant b - i;
    */
    for (int i = 0; i < b; ++i) {
        fact_b *= (i + 1);
    }

    // The quotient is guaranteed to be an integer by the requires a <= b.
    int quotient = fact_b / fact_a;

    // The last digit is quotient % 10.
    return quotient % 10;
}
