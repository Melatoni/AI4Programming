// Task ID: 3
// Generation: 5

/*@
  logic integer sum_array(integer n, integer (*arr)[n]);
  
  axiom sum_array_base: \forall integer n; n <= 0 ==> sum_array(n, ?);
  
  axiom sum_array_rec: \forall integer n; n > 0 ==> sum_array(n, arr) == arr[0][0] + sum_array(n - 1, arr + 1);

  axiom sum_array_non_negative: \forall integer n; \forall integer (*arr)[n]; (\forall integer i; 0 <= i < n ==> arr[i][0] >= 0) ==> sum_array(n, arr) >= 0;

*/

/*@ requires \valid(arr) && n > 0;
    requires \forall integer i; 0 <= i < n ==> arr[i] >= 0;
    assigns \nothing;
    ensures \result == (sum_array(n, arr) > 0 ? 1 : 0);
*/
int is_sum_positive(int n, int (*arr)[n]){
  /*@ loop invariant 0 <= i <= n;
      loop invariant sum_array(i, arr) == sum_array(i,arr);
      loop assigns i;
      loop variant n - i;
  */
  int i = 0;
  int sum = 0;
  while(i < n){
    sum += arr[i][0];
    i++;
  }
  return (sum > 0? 1:0);
}


/*@ requires \valid(arr) && n > 0;
    assigns \nothing;
    ensures \result == 1 ==> (\exists integer i; 0 <= i < n; arr[i] == 0);
*/
int contains_zero(int n, int (*arr)[n]){
  /*@ loop invariant 0 <= i <= n;
      loop assigns i;
      loop variant n - i;
  */
  int i = 0;
  while(i < n){
    if(arr[i][0] == 0) return 1;
    i++;
  }
  return 0;
}
