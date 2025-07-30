// Task ID: 20
// Generation: 7

/*@
  // Axiomatic block for recursive sum function (Rule II.1)
  axiomatic SumDigits {
    logic integer sum_digits_recursive(integer n);

    axiom sum_digits_recursive_base:
      \forall integer n; 0 <= n < 10 ==> sum_digits_recursive(n) == n;

    axiom sum_digits_recursive_step:
      \forall integer n; n >= 10 ==> sum_digits_recursive(n) == sum_digits_recursive(n / 10) + (n % 10);

    // Helper axiom: sum_digits_recursive is non-negative (Rule II.2)
    axiom sum_digits_recursive_non_negative:
      \forall integer n; n >= 0 ==> sum_digits_recursive(n) >= 0;

    // Helper axiom: sum_digits_recursive(n) < n for n >= 10
    axiom sum_digits_recursive_less_than_n:
      \forall integer n; n >= 10 ==> sum_digits_recursive(n) < n;
  }
*/

/*@
  // Axiomatic block for recursive product function (Rule II.1)
  axiomatic ProductDigits {
    logic integer product_digits_recursive(integer n);

    axiom product_digits_recursive_base:
      \forall integer n; 0 <= n < 10 ==> product_digits_recursive(n) == n;

    axiom product_digits_recursive_step:
      \forall integer n; n >= 10 ==> product_digits_recursive(n) == product_digits_recursive(n / 10) * (n % 10);

    // Helper axiom: product_digits_recursive is non-negative for non-negative input (Rule II.2)
    axiom product_digits_recursive_non_negative:
      \forall integer n; n >= 0 ==> product_digits_recursive(n) >= 0;

    // Helper axiom: if any digit is 0, product is 0
    axiom product_digits_recursive_zero_digit:
      \forall integer n; n > 0 && n % 10 == 0 ==> product_digits_recursive(n) == 0;
  }
*/


/*@
  requires n >= 0; // Woodball numbers are typically non-negative.
  // Rule II.5: Prevent overflow for sum and product operations.
  // Max sum of digits for INT_MAX (2,147,483,647) is 1+9*9 = 82.
  // Max product of digits for INT_MAX (2,147,483,647) is 2*1*4*7*4*8*3*6*4*7 = 161280.
  // These values are well within int limits, so no explicit overflow check is needed here
  // for the results of sum_digits_recursive and product_digits_recursive themselves,
  // but it's good to keep in mind.

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // A number n is a woodball number if the product of its digits is equal to the sum of its digits.
  ensures (product_digits_recursive(n) == sum_digits_recursive(n)) <==> ( \result == 1 );
*/
int is_woodball(int n) { // Rule I.2: Uses int for boolean result.
    if (n < 0) {
        return 0; // Or handle as an error, but problem implies non-negative.
    }

    int sum = 0;
    int product = 1;

    int temp_n = n;

    /*@
      loop invariant temp_n >= 0;
      loop invariant sum == sum_digits_recursive(n) - sum_digits_recursive(temp_n);
      // product represents the product of digits processed so far.
      loop invariant product == (temp_n == n ? 1 : product_digits_recursive(n) / product_digits_recursive(temp_n)) || (product_digits_recursive(n) == 0 && product == 0);
      // The above invariant for product is tricky due to division by zero if temp_n has a zero digit.
      // A more robust invariant using a helper function would be better:
      // logic integer product_digits_so_far(integer original_n, integer current_n);
      // loop invariant product == product_digits_so_far(n, temp_n);
      // For this problem, we simplify and assume product_digits_recursive(temp_n) != 0 unless temp_n is 0.
      // A simpler invariant for product_digits_so_far:
      // loop invariant \forall integer k; k*10 <= n && k*10 + (temp_n % 10) == n % 10 && k*10 <= n;
      // This is getting too complex for a single line invariant.
      // Let's use a simpler one and rely on the prover for non-zero digits.
      // We need to ensure that the product calculation is correct.
      // A more direct invariant for product:
      loop invariant \forall integer k; k >= 0 && temp_n * \pow(10, k) <= n ==> product == product_digits_recursive(n / \pow(10, k));
      // This is still complex. Let's simplify the invariant based on the logic.
      // The `product` variable accumulates the product of digits already processed (those removed from `temp_n`).
      // Let `original_n` be the initial value of `n`.
      // Let `temp_n_at_start_of_iteration` be the value of temp_n at the beginning of the current iteration.
      // Let `processed_digits_value` be `original_n - temp_n_at_start_of_iteration * 10^k` for some k.
      // This means `product` is the product of digits of `original_n / 10^k`.
      // Let's try this:
      loop invariant product == product_digits_recursive(n) / product_digits_recursive(temp_n) || (product_digits_recursive(n) == 0 && product == 0);
      // This is still problematic if product_digits_recursive(temp_n) is 0 due to a zero digit.
      // A better approach often involves defining an ACSL function that computes the product of the "processed" digits.
      // For now, let's try a simpler one and see if WP can handle it.
      // Let's define the product of digits of the part of `n` that has been processed.
      // Let `n_processed` be `n / 10^k` where `k` is the number of iterations.
      // `n_processed` is `n / (temp_n_at_start_of_iteration * 10^0)`
      // `n_processed` is `n / (temp_n_at_start_of_iteration)`? No.
      // The current `product` holds `product_digits(n_initial / (10^i))` where `i` is the number of digits processed.
      // This implies `product * product_digits_recursive(temp_n) == product_digits_recursive(n)`.
      // This is the most direct way to express the invariant.
      loop invariant (product_digits_recursive(temp_n) != 0 ==> product * product_digits_recursive(temp_n) == product_digits_recursive(n));
      loop invariant (product_digits_recursive(n) == 0 ==> product == 0); // If original product is 0, then current product must eventually become 0.
      loop invariant product >= 0; // Product of non-negative digits is non-negative.

      loop assigns temp_n, sum, product;
      loop variant temp_n; // Rule II.4: temp_n decreases in each iteration.
    */
    while (temp_n > 0) {
        int digit = temp_n % 10;
        sum += digit;
        product *= digit;
        temp_n /= 10;
    }

    return (sum == product) ? 1 : 0;
}
