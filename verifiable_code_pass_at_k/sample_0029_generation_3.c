// Task ID: 29
// Generation: 3

/*@ axiomatic OddOccurrence {
  @   logic integer count_occurrences{L}(int *a, integer n, int val);
  @
  @   axiom count_occurrences_base{L}:
  @     \forall int *a, integer n, int val;
  @       n <= 0 ==> count_occurrences(a, n, val) == 0;
  @
  @   axiom count_occurrences_rec{L}:
  @     \forall int *a, integer n, int val;
  @       n > 0 ==> count_occurrences(a, n, val) ==
  @         (a[n-1] == val ? 1 : 0) + count_occurrences(a, n-1, val);
  @
  @   // Rule II.2: Helper axiom to prove that count is non-negative
  @   axiom count_occurrences_non_negative{L}:
  @     \forall int *a, integer n, int val;
  @       n >= 0 ==> count_occurrences(a, n, val) >= 0;
  @ }
  @*/

/*@
  @ requires \valid_read(a + (0..n-1));
  @ requires n >= 0;
  @
  @ // Rule II.5: Ensure there is exactly one element with an odd count
  @ requires \exists int val;
  @   count_occurrences(a, n, val) % 2 == 1 &&
  @   (\forall int other_val; other_val != val ==> count_occurrences(a, n, other_val) % 2 == 0);
  @
  @ assigns \nothing;
  @
  @ ensures (\exists integer i; 0 <= i < n && count_occurrences(a, n, a[i]) % 2 == 1) <==> (\result == a[i]);
  @ ensures count_occurrences(a, n, \result) % 2 == 1;
  @*/
int find_odd_occurrence(int *a, int n) {
  int result = 0;

  /*@
    @ loop invariant 0 <= i <= n;
    @ loop invariant \forall integer k; 0 <= k < i ==> (\exists integer l; 0 <= l < i && a[l] == a[k]) ==> (count_occurrences(a, i, a[k]) % 2 == 0 <==> count_occurrences(a, n, a[k]) % 2 == 0);
    @ // This invariant is challenging. A simpler one is to track the XOR sum directly.
    @ loop invariant \forall integer k; 0 <= k < i ==> (count_occurrences(a, i, a[k]) % 2 == 1) <==> (result ^ a[k] == 0);
    @ loop invariant (count_occurrences(a, i, a[k]) % 2 == 0) <==> (result ^ a[k] == a[k]);

    @ loop invariant \forall integer k; 0 <= k < i ==> (count_occurrences(a, i, a[k]) % 2 == 1) <==> (\exists integer j; 0 <= j < i && a[j] == a[k] && (\forall integer l; 0 <= l < j ==> a[l] != a[k]) && (count_occurrences(a, i, a[k]) % 2 == 1));
    @ loop invariant \forall integer k; 0 <= k < n; (count_occurrences(a, i, a[k]) % 2 == 1) <==> (\exists integer j; 0 <= j < i && a[j] == a[k] && (count_occurrences(a, i, a[k]) % 2 == 1));
    @ loop invariant result == (\xor integer j; 0 <= j < i; a[j]);
    @ loop assigns i, result;
    @ loop variant n - i;
  */
  for (int i = 0; i < n; i++) {
    result ^= a[i];
  }

  return result;
}
