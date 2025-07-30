// Task ID: 22
// Generation: 9

/*@ axiomatic FirstDuplicate {
  @   logic integer first_duplicate_index{L}(int* a, integer n) reads a[0..n-1];
  @
  @   axiom first_duplicate_index_base{L}:
  @     \forall int* a, integer n;
  @       (n <= 1 || (\forall integer i, j; 0 <= i < j < n ==> a[i] != a[j])) ==>
  @       first_duplicate_index(a, n) == -1;
  @
  @   axiom first_duplicate_index_recursive{L}:
  @     \forall int* a, integer n;
  @       n > 1 && (\exists integer j; 0 <= j < n - 1 && a[n-1] == a[j]) ==>
  @       first_duplicate_index(a, n) == (
  @         \let k = \min integer j; 0 <= j < n - 1 && a[n-1] == a[j];
  @         if first_duplicate_index(a, n-1) == -1 then k
  @         else if k < first_duplicate_index(a, n-1) then k
  @         else first_duplicate_index(a, n-1)
  @       );
  @
  @   axiom first_duplicate_index_recursive_no_duplicate{L}:
  @     \forall int* a, integer n;
  @       n > 1 && (\forall integer j; 0 <= j < n - 1 ==> a[n-1] != a[j]) ==>
  @       first_duplicate_index(a, n) == first_duplicate_index(a, n-1);
  @ }
  @*/

/*@
  @ requires n >= 0;
  @ requires \valid_read_range(a, 0, n - 1);
  @
  @ assigns \nothing;
  @
  @ ensures (first_duplicate_index(a, n) != -1) <==> (\result != -1);
  @ ensures (\result != -1) ==> (0 <= \result < n);
  @ ensures (\result != -1) ==> (\exists integer j; 0 <= j < \result && a[\result] == a[j]);
  @ ensures (\result != -1) ==> (\forall integer k; 0 <= k < \result ==>
  @   (\forall integer l; 0 <= l < k ==> a[k] != a[l]));
  @ ensures (\result == -1) ==> (\forall integer i, j; 0 <= i < j < n ==> a[i] != a[j]);
  @*/
int find_first_duplicate(int* a, int n) {
    if (n <= 1) {
        return -1;
    }

    /*@
      @ loop invariant 0 <= i <= n;
      @ loop invariant \forall integer k; 0 <= k < i ==>
      @   (\forall integer l; 0 <= l < k ==> a[k] != a[l]);
      @ loop assigns i;
      @ loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        /*@
          @ loop invariant 0 <= j <= i;
          @ loop invariant \forall integer k; 0 <= k < j ==> a[i] != a[k];
          @ loop assigns j;
          @ loop variant i - j;
        */
        for (int j = 0; j < i; ++j) {
            if (a[i] == a[j]) {
                return i;
            }
        }
    }
    return -1;
}
