// Task ID: 20
// Generation: 4

/*@ axiomatic Woodball {
  logic integer sum_digits(integer n) reads n;

  axiom sum_digits_base:
    \forall integer n; 0 <= n <= 9 ==> sum_digits(n) == n;

  axiom sum_digits_recursive:
    \forall integer n; n > 9 ==> sum_digits(n) == sum_digits(n / 10) + (n % 10);

  // Rule II.2: Helper axiom for sum_digits to prove a property about its range
  // This helps the prover deduce properties about the sum of digits later.
  // The maximum sum of digits for a 32-bit integer (2,147,483,647) is
  // sum_digits(1,999,999,999) = 1 + 9*8 = 73.
  // sum_digits(2,147,483,647) = 2+1+4+7+4+8+3+6+4+7 = 46.
  // The maximum sum of digits for any positive integer n is bounded.
  // For n >= 0, sum_digits(n) >= 0.
  // For n > 0, sum_digits(n) >= 1.
  axiom sum_digits_positive:
    \forall integer n; n > 0 ==> sum_digits(n) > 0;
}
*/

/*@
  requires n >= 0;
  // Rule II.5: Preventing potential overflow for sum_digits(n) * sum_digits(n)
  // The maximum sum of digits for a 32-bit int is 46. 46 * 46 = 2116, which fits in int.
  // However, to be safe and demonstrate the rule, we can add a bound based on the sum_digits range.
  // No strict upper bound on n is needed for sum_digits_recursive to avoid overflow itself,
  // as it only involves division and modulo.
  // The multiplication sum_digits(n) * sum_digits(n) must not overflow.
  // The maximum sum of digits for a 32-bit int (2^31 - 1) is 46.
  // 46 * 46 = 2116, which is well within INT_MAX.
  // So, no explicit requires for n regarding overflow of sum_digits(n) * sum_digits(n) is strictly needed
  // if sum_digits(n) is guaranteed to be within the range of a few thousands.
  // But for demonstration purposes, let's consider a scenario where it *could* overflow if sum_digits was larger.
  // For this specific problem, based on INT_MAX, sum_digits(n) <= 46.
  // So (sum_digits(n) * sum_digits(n)) <= 46*46 = 2116. This will not overflow int.
  // We'll keep the requires minimal as the type `int` already implies its max value.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (n == sum_digits(n) * sum_digits(n)) <==> (\result == 1);
*/
int is_woodball(int n) { // Rule I.2: Uses int for boolean-like return value.
    if (n < 0) {
        return 0; // Woodball numbers are non-negative.
    }

    int temp = n;
    int digit_sum = 0;

    /*@
      loop invariant temp >= 0;
      loop invariant digit_sum == sum_digits(\old(temp) - temp); // This invariant is tricky.
      // A better invariant for digit_sum:
      // loop invariant digit_sum == sum_digits(\at(n, Pre) / (temp * \pow(10, (int)(\log10(\at(n, Pre))) - (int)(\log10(temp))))); // Too complex
      // The simplest correct invariant for digit_sum is:
      // loop invariant digit_sum == sum_digits_of_processed_digits(n, temp);
      // Let's define a logic function to represent the sum of digits of the part of n that has been processed.
      // This is a common pattern for digit manipulation loops.
      // Let's assume n_original is the value of n at the start of the function.
      // The "processed" part of the number is n_original % (10^k) where temp = n_original / (10^k).
      // The sum of digits is sum_digits(n_original / (10^k)) + sum_digits(n_original % (10^k)).
      // This is getting too complex for a simple sum of digits.
      // A simpler invariant for digit_sum:
      // loop invariant \forall integer k; k >= 0 && (\at(n, Pre) / (\pow(10, k))) == temp ==> digit_sum == sum_digits(\at(n, Pre) % (\pow(10, k))); // This is also complex.

      // Let's use a simpler invariant:
      // digit_sum accumulates the sum of digits of (n - temp)
      // No, it accumulates the sum of digits of the number formed by the digits already processed.
      // Example: n=123.
      // Iter 1: temp=12, digit_sum=3.  sum_digits(3) == 3.
      // Iter 2: temp=1,  digit_sum=3+2=5. sum_digits(23) == 5.
      // Iter 3: temp=0,  digit_sum=5+1=6. sum_digits(123) == 6.
      // So, digit_sum == sum_digits(\at(n, Pre) - temp * \pow(10, k)) where k is number of iterations.
      // This is the correct way:
      // loop invariant digit_sum == sum_digits(\at(n, Pre)) - sum_digits(temp); // No, this is incorrect.
      // A common pattern:
      // loop invariant digit_sum == sum_digits_of_original_number_up_to_current_temp(n, temp);
      // Let's define it using the axiomatic function sum_digits:
      // At each iteration, `digit_sum` holds the sum of digits of the number `n` without its `temp` part.
      // `n_original` is the initial value of `n`.
      // `temp` is `n_original / (10^k)` for some `k`.
      // `digit_sum` is `sum_digits(n_original % (10^k))`.
      // This is exactly what the `sum_digits` function does recursively.
      // So, the invariant should state that `digit_sum` is what `sum_digits` would return for the *processed* part.
      // The `temp` variable always holds the unprocessed part.
      // The sum of digits of the original number `n` is `sum_digits(temp) + sum_digits(n % (10^k))`.
      // This is the invariant:
      loop invariant \at(n, Pre) == temp * \pow(10, \at(I, LoopEntry) - \at(I, Here)) + (\at(n, Pre) % \pow(10, \at(I, LoopEntry) - \at(I, Here))); // I is a dummy loop counter.
      // This is simpler:
      loop invariant digit_sum == sum_digits_of_part_processed(\at(n, Pre), temp); // Need to define sum_digits_of_part_processed.
      // A simpler invariant for `digit_sum` is to relate it to a property of `n`.
      // The state of `n` is unchanged. `temp` is `n` divided by some power of 10.
      // `digit_sum` is the sum of digits of `n` that have been "extracted".
      // This can be expressed as: `digit_sum + sum_digits(temp)` is the sum of digits of current `n` if `temp` was `0`.
      // The best invariant for this loop:
      loop invariant digit_sum + sum_digits(temp) == sum_digits(\at(n, Pre));
      loop assigns temp, digit_sum;
      // Rule II.4: Loop variant for termination.
      loop variant temp;
    */
    while (temp > 0) {
        digit_sum += temp % 10;
        temp /= 10;
    }

    // Rule II.5: Preventing i*i overflow.
    // We need to ensure that digit_sum * digit_sum does not overflow before comparison.
    // As established, max digit_sum is 46, so 46*46 = 2116, which fits in `int`.
    // So, no explicit overflow check is needed here for `digit_sum * digit_sum`.
    if (digit_sum * digit_sum == n) {
        return 1;
    } else {
        return 0;
    }
}
