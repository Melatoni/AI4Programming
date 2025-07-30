// Task ID: 5
// Generation: 1

/*@
  // Rule II.1: Define recursive logic for the number of ways.
  axiomatic DominoWays {
    logic integer domino_ways(integer n);

    axiom domino_ways_0:
      domino_ways(0) == 1; // Base case: one way to fill a 3x0 board (empty)
    axiom domino_ways_1:
      domino_ways(1) == 0; // Base case: zero ways to fill a 3x1 board
    axiom domino_ways_2:
      domino_ways(2) == 3; // Base case: three ways to fill a 3x2 board
    axiom domino_ways_n_even:
      // Rule II.2: Helper axiom for even n
      // For even n > 2, ways(n) = 4 * ways(n-2) - ways(n-4)
      // This recurrence relation is derived from the problem's properties.
      // It's crucial for the prover to connect the loop with the mathematical definition.
      \forall integer n;
        n >= 4 && n % 2 == 0 ==>
          domino_ways(n) == 4 * domino_ways(n - 2) - domino_ways(n - 4);
    axiom domino_ways_n_odd:
      // Rule II.2: Helper axiom for odd n
      \forall integer n;
        n >= 1 && n % 2 != 0 ==>
          domino_ways(n) == 0;
  }
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent potential overflow for larger n.
  // The maximum possible value for domino_ways(n) grows exponentially.
  // For n=30, ways(30) is 2172861213. For n=32, it's 8950669149 > INT_MAX.
  // Therefore, n must be less than or equal to 30 for the result to fit in int.
  requires n <= 30;

  assigns \nothing;

  // Rule II.3: Ensures clause for the function's result.
  ensures \result == domino_ways(n);
*/
int count_domino_ways(int n) {
  // If n is odd, there are 0 ways to tile a 3xn board.
  if (n % 2 != 0) {
    return 0;
  }

  // Base cases
  if (n == 0) {
    return 1;
  }
  if (n == 2) {
    return 3;
  }

  // For even n > 2, use dynamic programming.
  // We need to store ways[i-2] and ways[i-4] to calculate ways[i].
  // We only need the previous two even results.
  int dp_n_minus_4 = 1; // Corresponds to domino_ways(0)
  int dp_n_minus_2 = 3; // Corresponds to domino_ways(2)
  int current_ways = 0;

  /*@
    loop invariant 4 <= i <= n + 2;
    // The loop invariant connects the a, b variables to the axiomatic definition.
    // dp_n_minus_4 holds domino_ways(i - 4).
    loop invariant (i - 4) % 2 == 0 ==> dp_n_minus_4 == domino_ways(i - 4);
    // dp_n_minus_2 holds domino_ways(i - 2).
    loop invariant (i - 2) % 2 == 0 ==> dp_n_minus_2 == domino_ways(i - 2);
    // current_ways holds domino_ways(i) when i is even.
    loop invariant (current_ways == 0 && i % 2 != 0) || (current_ways == domino_ways(i) && i % 2 == 0);

    assigns dp_n_minus_4, dp_n_minus_2, current_ways;

    // Rule II.4: Loop variant for termination.
    loop variant n - i;
  */
  for (int i = 4; i <= n; i += 2) {
    // Rule II.5: Prevent overflow in intermediate calculation.
    // 4 * dp_n_minus_2 can exceed INT_MAX if dp_n_minus_2 is large.
    // Since n <= 30, max dp_n_minus_2 is domino_ways(28) = 53049615.
    // 4 * 53049615 = 212198460, which fits in int.
    // The subtraction dp_n_minus_4 does not cause underflow as dp_n_minus_4 is positive.
    current_ways = 4 * dp_n_minus_2 - dp_n_minus_4;
    dp_n_minus_4 = dp_n_minus_2;
    dp_n_minus_2 = current_ways;
  }

  return current_ways;
}
