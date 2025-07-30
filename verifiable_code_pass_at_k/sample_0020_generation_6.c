// Task ID: 20
// Generation: 6

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay not applicable here.

  // Rule II.5: Preconditions to prevent overflow for large numbers.
  // The maximum value for an `int` is typically 2,147,483,647.
  // The largest number `num` could be such that `num * 10` does not overflow.
  // If `num` is `INT_MAX / 10`, `num * 10` is roughly `INT_MAX`.
  // `get_digits_product` could overflow if `num` has many large digits.
  // For `get_sum_of_digits`, the sum of digits of `INT_MAX` (2147483647) is 2+1+4+7+4+8+3+6+4+7 = 46. This won't overflow.
  // The product of digits, however, can overflow quickly. For example, 999999999 has 9^9, which is huge.
  // We need to constrain `num` to prevent intermediate products from overflowing `int`.
  // A safe upper bound for `num` to prevent product overflow depends on the maximum product of digits.
  // For `int`, 2^31 - 1. Max product of digits for a 9-digit number cannot exceed 9^9 = 387,420,489.
  // For a 10-digit number like 2147483647, the product is 2*1*4*7*4*8*3*6*4*7 = 32256.
  // For a number like 99999, product is 9^5 = 59049.
  // For a number like 999999, product is 9^6 = 531441.
  // For a number like 9999999, product is 9^7 = 4782969.
  // For a number like 99999999, product is 9^8 = 43046721.
  // For a number like 999999999, product is 9^9 = 387420489.
  // All these products fit into a standard 32-bit signed int.
  // The constraint `num * 10` is for `temp = num; temp /= 10;` loop, to avoid `temp` becoming 0 for `num=0`.
  // A simple `num >= 0` is sufficient for this specific problem as negative numbers are not usually woodball candidates.
  requires num >= 0;

  // Axiomatic definition for sum of digits
  axiomatic SumOfDigits {
    logic integer sum_of_digits_rec(integer n);

    axiom sum_of_digits_base:
      \forall integer n; n >= 0 && n < 10 ==> sum_of_digits_rec(n) == n;

    axiom sum_of_digits_rec_step:
      \forall integer n; n >= 10 ==> sum_of_digits_rec(n) == sum_of_digits_rec(n / 10) + (n % 10);

    // Rule II.2: Helper axiom for recursive logic.
    // This axiom helps the prover understand properties of the sum_of_digits_rec function.
    // If n is non-negative, its sum of digits is also non-negative.
    axiom sum_of_digits_non_negative:
      \forall integer n; n >= 0 ==> sum_of_digits_rec(n) >= 0;
  }

  // Axiomatic definition for product of digits
  axiomatic ProductOfDigits {
    logic integer product_of_digits_rec(integer n);

    axiom product_of_digits_base:
      \forall integer n; n >= 0 && n < 10 ==> product_of_digits_rec(n) == n;

    axiom product_of_digits_rec_step:
      \forall integer n; n >= 10 ==> product_of_digits_rec(n) == product_of_digits_rec(n / 10) * (n % 10);

    // Rule II.2: Helper axiom for recursive logic.
    // If n is non-negative, its product of digits is also non-negative.
    axiom product_of_digits_non_negative:
      \forall integer n; n >= 0 ==> product_of_digits_rec(n) >= 0;

    // A digit is 0, then product is 0.
    axiom product_of_digits_zero_digit:
      \forall integer n; n >= 0 && (\exists integer k; k >= 0 && n / (10 * k) % 10 == 0) ==> product_of_digits_rec(n) == 0;
  }

  // Rule II.3: Ensures clause using logical equivalence for boolean-like function.
  // A number `num` is a woodball number if the sum of its digits equals the product of its digits.
  ensures (\result == 1) <==> (sum_of_digits_rec(num) == product_of_digits_rec(num));
  assigns \nothing;
*/
int is_woodball(int num) {
    if (num < 0) {
        return 0; // Negative numbers are not typically considered woodball numbers.
    }

    int sum_digits = 0;
    int product_digits = 1;
    int temp = num;

    // Handle the special case of 0, as the loop won't run for it.
    // Sum of digits of 0 is 0, product of digits of 0 is 0. So 0 is a woodball number.
    if (temp == 0) {
        return 1;
    }

    /*@
      loop invariant temp >= 0;
      loop invariant \at(num, Pre) == \at(temp, LoopEntry) * \pow(10, \at(loop_iter, LoopEntry)) + (\at(temp, LoopEntry) < \at(num, Pre) ? \at(num, Pre) % \pow(10, \at(loop_iter, LoopEntry)) : 0);
      loop invariant sum_digits == sum_of_digits_rec(\at(num, Pre) / \pow(10, \at(loop_iter, LoopEntry) - 1)) - sum_of_digits_rec(temp);
      loop invariant product_digits == product_of_digits_rec(\at(num, Pre) / \pow(10, \at(loop_iter, LoopEntry) - 1)) / product_of_digits_rec(temp);

      // We need more precise invariants for sum_digits and product_digits.
      // Let original_num be the value of num at function entry.
      // Let current_part be original_num / (10^k) where k is the number of digits processed so far.
      // The `temp` variable holds `original_num / (10^k)`.
      // The `sum_digits` is the sum of digits of `original_num % (10^k)`.
      // The `product_digits` is the product of digits of `original_num % (10^k)`.

      // A more robust invariant using the axiomatic functions:
      loop invariant temp >= 0;
      // sum_digits accumulates the sum of digits of `num` that have already been processed (i.e., `num % power_of_10`).
      // `\at(num, Pre)` is the original number.
      // The digits processed are those from the right.
      // `\at(num, Pre) / temp` represents the power of 10 that `temp` has been divided by.
      // Let's refine the invariant using `num / temp` as the multiplier.
      // `sum_digits` is the sum of digits of `num` from `num % (10^k)` where `k` is the number of divisions.
      // `product_digits` is the product of digits of `num` from `num % (10^k)`.
      // This is tricky. Let's express it in terms of the digits removed.
      // Let `original_num` be `num` at the start of the function.
      // At each iteration, `temp` becomes `original_num / 10^i` for some `i`.
      // `sum_digits` is `sum_of_digits_rec(original_num) - sum_of_digits_rec(temp)`. NO, this is wrong.
      // `sum_digits` is the sum of digits of `original_num % (original_num / temp)`.
      // `product_digits` is the product of digits of `original_num % (original_num / temp)`.

      // Let's use `\at(num, Pre)` to denote the original value of `num`.
      // `sum_digits` is the sum of digits of `\at(num, Pre)` excluding those in `temp`.
      loop invariant sum_digits == sum_of_digits_rec(\at(num, Pre)) - sum_of_digits_rec(temp) + sum_of_digits_rec(temp) - sum_of_digits_rec(temp / 10) - (temp % 10); // This is just getting complicated.

      // A simple approach for the loop invariants:
      // sum_digits represents the sum of digits of `\at(num, Pre)` that have been processed so far.
      // product_digits represents the product of digits of `\at(num, Pre)` that have been processed so far.
      // Let `original_num` be the value of `num` at the start.
      // Let `processed_part` be `original_num / temp`. This is `10^k` where `k` is number of digits processed.
      // The digits processed are `original_num % processed_part`.
      // This requires `\pow` which is not directly available in standard ACSL.
      // Let's use `temp` and `num` to describe the state.
      // `temp` starts as `num` and becomes `0`.
      // `num` is the original value.
      // `temp_at_entry` is the value of `temp` at the beginning of the current iteration.
      // `sum_digits` holds the sum of the digits of `num` that are *not* part of `temp`.
      // `product_digits` holds the product of the digits of `num` that are *not* part of `temp`.

      // Let's define the parts more clearly:
      // `processed_digits_value`: \at(num, Pre) - temp * (\at(num, Pre) / temp)
      // `processed_digits_value`: (original_num % (current_temp * 10)) / 10
      // This is still complex. Let's simplify the invariant based on the original `num` and the current `temp`.

      // The loop processes digits from right to left.
      // `sum_digits` contains the sum of digits of `(\at(num, Pre) / 10^k) % 10` for `k` from 0 up to `(number of digits in original_num) - (number of digits in temp) - 1`.
      // `product_digits` contains the product of digits of `(\at(num, Pre) / 10^k) % 10` for `k` from 0 up to `(number of digits in original_num) - (number of digits in temp) - 1`.

      // A better invariant:
      // The sum of digits of the original number (`num` at Pre)
      // can be split into the sum of digits of `temp` and the sum of digits of the part that has been processed.
      // `sum_digits` is the sum of digits of `(\at(num, Pre) - temp * \pow(10, count_digits(temp)))`. This is wrong.

      // Let's use the axiomatic functions directly for the invariant:
      // `sum_digits` is the sum of digits processed so far.
      // `product_digits` is the product of digits processed so far.
      // This is hard because `temp` is changing.

      // Let's use the definition of `sum_of_digits_rec` and `product_of_digits_rec`:
      // `sum_digits` is the sum of `digit_i` for `i` from 0 to `k-1` where `k` is number of digits processed.
      // `digit_i = (\at(num, Pre) / 10^i) % 10`.
      // This is exactly `sum_of_digits_rec(\at(num, Pre)) - sum_of_digits_rec(temp)`.
      // But `sum_digits` is not just `sum_of_digits_rec(\at(num, Pre)) - sum_of_digits_rec(temp)`.
      // Example: num = 123
      // Iter 1: temp=12, digit=3. sum=3, prod=3.
      // sum_of_digits_rec(123) = 6. sum_of_digits_rec(12) = 3. 6-3 = 3. This matches.
      // product_of_digits_rec(123) = 6. product_of_digits_rec(12) = 2. 6/2 = 3. This matches.

      // Iter 2: temp=1, digit=2. sum=3+2=5, prod=3*2=6.
      // sum_of_digits_rec(123) = 6. sum_of_digits_rec(1) = 1. 6-1 = 5. This matches.
      // product_of_digits_rec(123) = 6. product_of_digits_rec(1) = 1. 6/1 = 6. This matches.

      // So, the invariants are indeed:
      loop invariant sum_digits == sum_of_digits_rec(\at(num, Pre)) - sum_of_digits_rec(temp);
      loop invariant product_digits == product_of_digits_rec(\at(num, Pre)) / (product_of_digits_rec(temp) == 0 ? 1 : product_of_digits_rec(temp));
      // Added `product_of_digits_rec(temp) == 0 ? 1 : product_of_digits_rec(temp)` to handle division by zero if `temp` contains a zero digit.
      // However, if `product_of_digits_rec(temp)` is 0, then `product_of_digits_rec(\at(num, Pre))` must also be 0
      // because `temp` is a prefix of `\at(num, Pre)`'s digits.
      // If `product_of_digits_rec(temp)` is 0, it means `temp` contains a 0 digit.
      // This also means `product_of_digits_rec(\at(num, Pre))` is 0.
      // So the invariant `product_digits == product_of_digits_rec(\at(num, Pre)) / product_of_digits_rec(temp)`
      // would become `0 == 0 / 0`, which is undefined.
      // This implies that if `product_of_digits_rec(temp)` is 0, `product_digits` should also be 0, and
      // `product_of_digits_rec(\at(num, Pre))` should be 0.
      // Let's refine the product invariant.

      // A better invariant for product_digits:
      // `product_digits` represents the product of digits of `\at(num, Pre) % (10^k)` where `k` is the number of digits processed.
      // `product_of_digits_rec(N)` is the product of ALL digits of N.
      // So, `product_digits` is `product_of_digits_rec(\at(num, Pre))` when `temp` is 0.
      // When `temp` is not 0, `product_digits` is the product of the digits of `\at(num, Pre)` that are *not* in `temp`.
      // Let's use `\at(num, Pre)` as the original number.
      // If `product_of_digits_rec(\at(num, Pre))` is 0, then `product_digits` will eventually be 0.
      // If `temp` contains a 0 digit, `product_of_digits_rec(temp)` will be 0.
      // The invariant for product needs to be careful about 0.
      // `product_digits` is the product of digits of `\at(num, Pre)` divided by the product of digits of `temp` (if `temp` has no 0 digit).
      // If `temp` has a 0 digit, then `product_of_digits_rec(temp)` is 0. And `product_of_digits_rec(\at(num, Pre))` is also 0.
      // In this case, `product_digits` should be 0.
      // So, the product invariant:
      loop invariant (product_of_digits_rec(temp) != 0 ==> product_digits == product_of_digits_rec(\at(num, Pre)) / product_of_digits_rec(temp));
      loop invariant (product_of_digits_rec(temp) == 0 ==> product_digits == 0);

      loop assigns temp, sum_digits, product_digits;
      // Rule II.4: Loop variant for termination.
      loop variant temp;
    */
    while (temp > 0) {
        int digit = temp % 10;

        // Rule II.5: Prevent overflow for sum_digits and product_digits.
        // sum_digits overflow: Max sum of digits for INT_MAX is 46. No overflow.
        // product_digits overflow: Max product of digits for INT_MAX is 32256. No overflow.
        // However, 999999999 has product 9^9 = 387420489, which fits.
        // But 2147483647 has product 32256.
        // If num was e.g., 9999999999 (larger than INT_MAX, but hypothetically), product could overflow.
        // Our `requires num >= 0` and `num` being `int` guarantees this is fine.
        sum_digits += digit;
        product_digits *= digit;

        temp /= 10;
    }

    return (sum_digits == product_digits);
}
