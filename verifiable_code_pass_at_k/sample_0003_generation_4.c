// Task ID: 3
// Generation: 4

/*@
  logic integer sum_array(integer n, integer (*a)[n]);
  
  axiom sum_array_base: \forall integer n; n <= 0 ==> sum_array(n, ?);
  axiom sum_array_rec: \forall integer n; n > 0 ==> sum_array(n, a) == a[0][0] + sum_array(n-1, a+1);

  axiom sum_non_negative: \forall integer n; \forall integer (*a)[n]; (\forall integer i; 0 <= i < n ==> a[0][i] >= 0) ==> sum_array(n, a) >= 0;

*/

/*@ requires \valid(arr) && n > 0;
    requires \forall integer i; 0 <= i < n ==> arr[i] > 1;
    assigns \nothing;
    ensures \result == 0 ==> \forall integer i; 0 <= i < n ==> \exists integer j; 2 <= j < arr[i] && arr[i] % j == 0;
    ensures \result != 0 ==> \exists integer i; 0 <= i < n && (\forall integer j; 2 <= j < arr[i] ==> arr[i] % j != 0);
*/
int are_all_non_prime(int n, int (*arr)[n]){
  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer k; 0 <= k < i ==> \exists integer j; 2 <= j < arr[k] && arr[k] % j == 0;
    loop assigns i;
    loop variant n - i;
  */
  for(int i = 0; i < n; i++){
      int is_prime = 1;
      /*@
        loop invariant 2 <= j <= arr[i];
        loop invariant is_prime == 1 ==> (\forall integer k; 2 <= k < j ==> arr[i] % k != 0);
        loop assigns j, is_prime;
        loop variant arr[i] - j;
      */
      for(int j = 2; j < arr[i]; j++){
          if(arr[i] % j == 0){
              is_prime = 0;
              break;
          }
      }
      if(is_prime == 1) return 1;
  }
  return 0;
}
