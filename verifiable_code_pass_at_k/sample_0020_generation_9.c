// Task ID: 20
// Generation: 9

/*@
  // Rule I.1: No standard library includes.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Not applicable here as no arrays.

  // Rule II.1: Recursive logic for complexity (not directly needed for this problem, but good to keep in mind).
  // Rule II.2: Helper axioms (not directly needed for this problem, but good to keep in mind).

  // Rule II.5: Prevent Runtime Errors (RTE)
  // For n >= 0, the digits are non-negative.
  // The sum of digits can overflow if n is very large.
  // Max sum of digits for int MAX (2,147,483,647) is 1+9*9 = 82.
  // Max product of digits for int MAX is 9^10, which overflows int.
  // Let's constrain n to ensure product of digits doesn't overflow `int`.
  // Max product for n up to 1,000,000,000 (10 digits). 9^9 = 387,420,489. This fits in int.
  // Let's constrain n to be positive.
  requires n >= 0;
  // If n has a 0 digit, product will be 0.
  // If n has a 1 digit, it doesn't change the product.
  // Max product of digits for n = 999,999,999 is 9^9 = 387,420,489. This fits in int.
  // Max sum of digits for n = 999,999,999 is 9*9 = 81. This fits in int.
  // So, `int` is sufficient for sum and product of digits for positive `int` inputs.
  // Thus, no specific `requires` for overflow for sum/product for `int` inputs.

  assigns \nothing;

  // Rule II.3: ensures clause for boolean-like functions uses logical equivalence.
  // A number is a woodball number if the product of its digits is equal to the sum of its digits.
  ensures (\exists integer temp_n;
            temp_n == \old(n) &&
            (\exists integer sum, product;
              sum == (if temp_n == 0 then 0 else \sum_digits(temp_n)) &&
              product == (if temp_n == 0 then 0 else \product_digits(temp_n)) &&
              sum == product
            )
          ) <==> (esult == 1);
*/
int is_woodball(int n) {
    if (n < 0) {
        return 0; // Woodball numbers are typically defined for non-negative integers.
    }

    if (n == 0) {
        return 1; // For n=0, sum=0, product=0, so sum == product.
    }

    int sum_digits = 0;
    int product_digits = 1;
    int temp_n = n;

    /*@
      loop invariant temp_n >= 0;
      loop invariant \forall integer k; k > temp_n ==> \old(temp_n) / (10^k) == 0;
      // Invariant for sum_digits: sum_digits contains the sum of digits of (\old(n) - temp_n).
      // This is hard to express precisely with \old and current temp_n.
      // A more practical invariant: sum_digits is the sum of digits already processed (from right to left).
      // Let original_n be the value of n at loop entry.
      // Let processed_digits_val = original_n % (10^k) where k is the number of digits processed.
      // sum_digits == sum of digits of (original_n % (10^(\text{number of digits processed}))).
      // product_digits == product of digits of (original_n % (10^(\text{number of digits processed}))).
      // A simpler invariant that WP can handle:
      // sum_digits is the sum of digits of (n_original % (10 ^ (number of digits processed)))
      // and product_digits is the product of digits of (n_original % (10 ^ (number of digits processed)))
      // But we are processing from right to left, `temp_n` becomes the *remaining* part.
      // So, `sum_digits` is the sum of digits of `\old(n) - temp_n * (appropriate power of 10)`
      // and `product_digits` is the product of digits of `\old(n) - temp_n * (appropriate power of 10)`.
      // This is very complex to formalize with ACSL for `sum_digits` and `product_digits`.
      // Let's use a simpler approach based on the `temp_n` value.

      // `sum_digits` is the sum of digits of `\old(n)` that are NOT in `temp_n`.
      // `product_digits` is the product of digits of `\old(n)` that are NOT in `temp_n`.
      // The `loop invariant` needs to relate `sum_digits` and `product_digits` to `n` and `temp_n`.
      // Let `\Digits(X)` be the set of digits of X.
      // `sum_digits == \sum_{d \in \Digits(\old(n) - temp_n * 10^k)} d` (where k is digits in temp_n)
      // `product_digits == \product_{d \in \Digits(\old(n) - temp_n * 10^k)} d`

      // A more abstract but verifiable invariant:
      // `sum_digits + \sum_digits(temp_n) == \sum_digits(\old(n))`
      // `product_digits * \product_digits(temp_n) == \product_digits(\old(n))`
      // This requires defining `\sum_digits` and `\product_digits` as logic functions.

      logic integer \sum_digits(integer val) =
        if val == 0 then 0
        else \sum_digits(val / 10) + (val % 10);

      logic integer \product_digits(integer val) =
        if val == 0 then 1 // Product of digits of 0 (empty set of digits) is 1, by convention for multiplication.
                           // Or, if we consider 0 itself, product is 0.
                           // For non-zero numbers, if a digit is 0, product is 0.
                           // For n=0, sum=0, product=0. In the loop, if n!=0, then no digit is 0 initially.
                           // If n has a 0 digit, product_digits becomes 0.
        else \product_digits(val / 10) * (val % 10);

      loop invariant temp_n >= 0;
      loop invariant sum_digits == \sum_digits(\old(n)) - \sum_digits(temp_n);
      loop invariant product_digits == (
        // If any digit processed so far was 0, product_digits is 0.
        // If temp_n has a 0 digit, then product_digits should also be 0 in the end.
        // This is complex. Let's simplify.
        // The product_digits == 0 if any digit of \old(n) up to `temp_n` was 0.
        // If temp_n is 0, it means all digits of \old(n) have been processed.
        // The product_digits starts at 1. If any digit is 0, product_digits becomes 0.
        // If there is no 0 digit, then product_digits is the product of digits processed.
        (product_digits == 0 || \product_digits(\old(n)) / \product_digits(temp_n) == product_digits)
      );
      // For product_digits, if any digit is 0, the product becomes 0.
      // The invariant should reflect this.
      // If product_digits is 0, it means some digit was 0.
      // If product_digits is not 0, it means no digit processed so far was 0.
      // And in that case, product_digits * \product_digits(temp_n) == \product_digits(\old(n)).

      // Let's refine the product_digits invariant.
      // `\has_zero_digit(val)`: logic function checking if val has a 0 digit.
      logic boolean \has_zero_digit(integer val) =
        if val == 0 then \false
        else (val % 10 == 0 || \has_zero_digit(val / 10));

      loop invariant sum_digits == \sum_digits(\old(n)) - \sum_digits(temp_n);
      loop invariant (product_digits == 0) <==> (\has_zero_digit(\old(n)) && !\has_zero_digit(temp_n));
      // If product_digits is not 0, then no processed digit was 0, and no digit in temp_n is 0.
      loop invariant (product_digits != 0) ==> (product_digits * \product_digits(temp_n) == \product_digits(\old(n)));

      loop assigns temp_n, sum_digits, product_digits;
      loop variant temp_n; // Rule II.4: A loop variant is mandatory for termination.
    */
    while (temp_n > 0) {
        int digit = temp_n % 10;
        sum_digits += digit;
        if (product_digits != 0) { // Only multiply if product hasn't already become 0
            product_digits *= digit;
        }
        temp_n /= 10;
    }

    if (sum_digits == product_digits) {
        return 1;
    } else {
        return 0;
    }
}
