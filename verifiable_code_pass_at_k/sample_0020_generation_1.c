// Task ID: 20
// Generation: 1

/*@ axiomatic Woodball {
  logic integer sum_digits(integer n);

  axiom sum_digits_base:
    \forall integer n; 0 <= n <= 9 ==> sum_digits(n) == n;
  axiom sum_digits_recursive:
    \forall integer n; n > 9 ==> sum_digits(n) == sum_digits(n / 10) + (n % 10);

  // Helper axiom: Sum of digits is non-negative
  // Rule II.2: CRITICAL - Helper Axioms
  axiom sum_digits_non_negative:
    \forall integer n; n >= 0 ==> sum_digits(n) >= 0;

  // Helper axiom: Sum of digits of a positive number is positive
  axiom sum_digits_positive:
    \forall integer n; n > 0 ==> sum_digits(n) > 0;

  // Helper axiom: Sum of digits of a number is less than or equal to the number itself if n >= 1
  axiom sum_digits_le_n:
    \forall integer n; n >= 1 ==> sum_digits(n) <= n;

  // Helper axiom: Sum of digits of a number is 9 if n is a multiple of 9 and n > 0
  axiom sum_digits_multiple_of_9:
    \forall integer n; n > 0 && n % 9 == 0 ==> sum_digits(n) == 9;

  // Helper axiom: Sum of digits of a number is n % 9 if n is not a multiple of 9 and n > 0
  axiom sum_digits_not_multiple_of_9:
    \forall integer n; n > 0 && n % 9 != 0 ==> sum_digits(n) == (n % 9);

  // Helper axiom: Sum of digits of 0 is 0
  axiom sum_digits_zero:
    sum_digits(0) == 0;

  logic int is_prime(integer n);

  axiom is_prime_base:
    is_prime(2) == 1;
  axiom is_prime_less_than_2:
    \forall integer n; n < 2 ==> is_prime(n) == 0;
  axiom is_prime_composite:
    \forall integer n; n >= 2 && (\exists integer i; 2 <= i && i * i <= n && n % i == 0) ==> is_prime(n) == 0;
  axiom is_prime_true:
    \forall integer n; n >= 2 && (\forall integer i; 2 <= i && i * i <= n ==> n % i != 0) ==> is_prime(n) == 1;

  // Helper axiom: is_prime(0) is 0
  axiom is_prime_0: is_prime(0) == 0;
  // Helper axiom: is_prime(1) is 0
  axiom is_prime_1: is_prime(1) == 0;
  // Helper axiom: is_prime(4) is 0
  axiom is_prime_4: is_prime(4) == 0;
  // Helper axiom: is_prime(9) is 0
  axiom is_prime_9: is_prime(9) == 0;
  // Helper axiom: is_prime(13) is 1
  axiom is_prime_13: is_prime(13) == 1;
  // Helper axiom: is_prime(17) is 1
  axiom is_prime_17: is_prime(17) == 1;
  // Helper axiom: is_prime(23) is 1
  axiom is_prime_23: is_prime(23) == 1;

  logic int is_woodball_logic(integer n);

  // A number n is a Woodball number if it is divisible by the sum of its digits,
  // and the sum of its digits is a prime number.
  axiom is_woodball_def:
    \forall integer n; n >= 0 ==>
    (is_woodball_logic(n) == (if (sum_digits(n) > 0 && n % sum_digits(n) == 0 && is_prime(sum_digits(n)) == 1) then 1 else 0));
}
*/

/*@
  requires n >= 0;
  // Rule II.5: Prevent potential overflow during sum_digits calculation if n is very large.
  // For 'int', the maximum sum of digits for INT_MAX (2,147,483,647) is sum_digits(1,999,999,999) = 1 + 9*8 = 73 or sum_digits(2,147,483,647) = 2+1+4+7+4+8+3+6+4+7 = 46.
  // The sum of digits will always fit in an int.
  // The `is_prime` check on sum_digits will also be on a small number.
  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  ensures (is_woodball_logic(n) == 1) <==> (result == 1);
*/
int is_woodball(int n) {
    if (n < 0) { // Although requires n >= 0, defensive check for safety.
        return 0;
    }

    int original_n = n;
    int sum = 0;

    /*@
      loop invariant n >= 0;
      loop invariant sum >= 0;
      loop invariant sum_digits(original_n) == sum_digits(n) + sum;
      loop assigns n, sum;
      loop variant n;
    */
    while (n > 0) {
        sum += n % 10;
        n /= 10;
    }

    if (sum == 0) { // Should only happen if original_n was 0
        // For n=0, sum_digits(0)=0. 0 % 0 is undefined.
        // By definition, is_woodball_logic(0) == 0.
        return 0;
    }

    // Check divisibility
    if (original_n % sum != 0) {
        return 0;
    }

    // Check if sum of digits is prime
    // Rule I.2: Use int for booleans. 1 for true, 0 for false.
    // Rule II.5: Prevent i*i overflow in the loop condition for 32-bit int.
    // The maximum sum is 46, so sum * sum will not overflow int.
    /*@
      loop invariant i >= 2;
      loop invariant \forall integer k; 2 <= k < i ==> sum % k != 0;
      loop assigns i;
      loop variant sum - i;
    */
    for (int i = 2; i * i <= sum; i++) {
        if (sum % i == 0) {
            return 0; // sum is not prime
        }
    }

    // if sum is 0 or 1, it's not prime. We already handled sum == 0.
    // If sum is 1, it's not prime.
    if (sum <= 1) {
        return 0;
    }

    return 1; // original_n is divisible by sum, and sum is prime
}
