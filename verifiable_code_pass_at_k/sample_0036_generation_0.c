// Task ID: 36
// Generation: 0

int` type. If `a` and `b` are `int`, then `a*10` could overflow.
The problem statement doesn't specify the range of `a` and `b`. Let's assume `a` and `b` are positive integers and fit within `int`.
Since `a < b` and `a, b >= 1`, we have `b >= 2`.
The maximum value of `int` is `INT_MAX`.
If `a` is `INT_MAX / 10`, then `a * 10` will overflow.
To get the `n`-th digit, we need to perform `n` multiplications by 10.
If `n` is large, `a` can become very large.

Let's refine the process to avoid overflow if possible.
We are interested in `(a * 10^n) / b` (integer division) modulo 10.
This is equivalent to `floor((a * 10^n) / b) % 10`.

This approach still requires computing `10^n` or `a * 10^n`, which can overflow.

The long division simulation is usually safer.
Let `current_numerator` be the value we are dividing by `b` at each step.
Initially, `current_numerator = a`.

For the 1st digit:
`current_numerator = a * 10`
`digit_1 = current_numerator / b`
`current_numerator = current_numerator % b`

For the 2nd digit:
`current_numerator = current_numerator * 10`
`digit_2 = current_numerator / b`
`current_numerator = current_numerator % b`

... and so on.

The `loop invariant` for `current_numerator` will be `0 <= current_numerator < b`.
The `loop variant` for the loop finding the `n`-th digit will be `n - i`.

The maximum initial `a` is `INT_MAX - 1` (since `a < b` and `b` can be `INT_MAX`).
If `a = INT_MAX / 10 - 1`, then `a * 10` will not overflow.
If `a = INT_MAX / 10`, then `a * 10` could be `INT_MAX - 9` (if `INT_MAX` ends in 9).
If `a = INT_MAX / 10 + 1`, then `a * 10` will overflow.

Let's assume `a` and `b` are within a range that `a * 10` does not overflow.
A reasonable `requires` clause might be `a <= INT_MAX / 10`.
And `b` is `b >= 2`.

/*@
  requires a >= 1;
  requires b >= 2;
  requires a < b; // Proper fraction
  
  // To prevent overflow in `current_numerator * 10`.
  // The maximum value of `current_numerator` is `b - 1`.
  // So, we need `(b - 1) * 10` to not overflow.
  // This means `b - 1 <= INT_MAX / 10`, or `b <= INT_MAX / 10 + 1`.
  // We can simplify this to `b <= INT_MAX / 10` for a safer bound,
  // or more precisely: `b <= INT_MAX / 10 + 1`.
  // Let's use `b <= INT_MAX / 10 + 1` which is equivalent to `10 * (b - 1) <= INT_MAX`.
  // Given `b` is `int`, `INT_MAX / 10 + 1` is a valid bound.
  requires b <= 214748364 + 1; // INT_MAX is 2147483647
  
  requires n >= 1; // n-th digit, so n must be at least 1.
  
  assigns \nothing;
  
  // The result is a digit between 0 and 9.
  ensures 0 <= \result <= 9;
*/
int get_nth_digit_of_fraction(int a, int b, int n) {
    int current_numerator = a;
    int digit;

    /*@
      loop invariant 1 <= i <= n + 1;
      // current_numerator is always the remainder after (i-1) steps of division.
      // After multiplying by 10, it's the new numerator for the current step.
      loop invariant 0 <= current_numerator < b;
      // The current_numerator is effectively (a * 10^(i-1)) % b
      // Frama-C/WP might struggle with this precise invariant directly.
      // Let's focus on bounds and non-overflow.
      
      loop assigns current_numerator, digit;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        // We need to ensure current_numerator * 10 does not overflow.
        // We have `current_numerator < b`.
        // The `requires b <= INT_MAX / 10 + 1` handles this.
        current_numerator *= 10;
        digit = current_numerator / b;
        current_numerator %= b;
    }
    return digit;
}
