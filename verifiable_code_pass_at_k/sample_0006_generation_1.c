// Task ID: 6
// Generation: 1

/*@ axiomatic BitDifference {
  @   logic integer count_set_bits_recursive(integer n) reads n;
  @   axiom count_set_bits_recursive_base:
  @     count_set_bits_recursive(0) == 0;
  @   axiom count_set_bits_recursive_step:
  @     \forall integer n; n > 0 ==> count_set_bits_recursive(n) == (n % 2) + count_set_bits_recursive(n / 2);
  @
  @   // Helper axiom to prove that count_set_bits_recursive returns a non-negative value.
  @   // This helps the prover with properties like the result being 1.
  @   axiom count_set_bits_recursive_non_negative:
  @     \forall integer n; n >= 0 ==> count_set_bits_recursive(n) >= 0;
  @ }
  @*/

/*@
  @ requires x >= 0;
  @ requires y >= 0;
  @
  @ assigns \nothing;
  @
  @ ensures (\result == 1) <==> (count_set_bits_recursive(x ^ y) == 1);
  @*/
int differ_by_one_bit(int x, int y) {
  int xor_result = x ^ y;
  int count = 0;

  /*@
    @ loop invariant count_set_bits_recursive(\at(xor_result, Pre)) == count_set_bits_recursive(xor_result) + count;
    @ loop invariant count >= 0;
    @ loop invariant xor_result >= 0;
    @ loop assigns xor_result, count;
    @ loop variant xor_result;
    @*/
  while (xor_result > 0) {
    if ((xor_result & 1) == 1) {
      count++;
    }
    xor_result >>= 1;
  }

  return count == 1;
}
