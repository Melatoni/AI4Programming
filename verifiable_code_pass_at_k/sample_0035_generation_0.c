// Task ID: 35
// Generation: 0

/*@
  // Rule II.5: Prevent overflow for n * (n + 1)
  // For 32-bit signed int, INT_MAX is 2,147,483,647.
  // We need n * (n + 1) <= INT_MAX.
  // Max n for which n * (n + 1) does not overflow is 46340.
  // 46340 * 46341 = 2147434740, which is < INT_MAX.
  // 46341 * 46342 = 2147527422, which overflows.
  requires n >= 0;
  requires n <= 46340;

  assigns \nothing;

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // The n-th rectangular number is n * (n + 1).
  ensures \result == n * (n + 1);
*/
int rectangular_number(int n) {
    return n * (n + 1);
}
