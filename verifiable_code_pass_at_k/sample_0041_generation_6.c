// Task ID: 41
// Generation: 6

/*@ axiomatic EvenFilter {
  @   logic int is_even(int x);
  @   axiom is_even_def:
  @     \forall int x; is_even(x) == (x % 2 == 0 ? 1 : 0);
  @ }
  @*/

/*@
  @ requires \valid_read(arr + (0..len-1));
  @ requires \valid_write(out + (0..len-1));
  @ requires len >= 0;
  @
  @ // Prevents potential overflow if len is very large (though unlikely for typical int sizes)
  @ // and ensures indices are within int range.
  @ requires len <= 2147483647;
  @
  @ assigns out[0..len-1], \result;
  @
  @ ensures \forall integer k; 0 <= k < \result ==> is_even(out[k]) == 1;
  @ ensures \forall integer k; \result <= k < len ==> out[k] == \old(out[k]); // out elements beyond new_len are unchanged
  @ ensures \forall integer i; 0 <= i < len ==>
  @   (is_even(arr[i]) == 1 ==> \exists integer j; 0 <= j < \result && out[j] == arr[i]);
  @ ensures \forall integer i; 0 <= i < len ==>
  @   (is_even(arr[i]) == 0 ==> \forall integer j; 0 <= j < \result && out[j] != arr[i]);
  @ ensures \result == (\numof(integer i; 0 <= i < len && is_even(arr[i]) == 1));
  @*/
int filter_even(int arr[], int len, int out[]) {
    int new_len = 0;
    /*@
      @ loop invariant 0 <= i <= len;
      @ loop invariant 0 <= new_len <= i;
      @ loop invariant \forall integer k; 0 <= k < new_len ==> is_even(out[k]) == 1;
      @ loop invariant \forall integer k; 0 <= k < i && is_even(arr[k]) == 1 ==>
      @   \exists integer j; 0 <= j < new_len && out[j] == arr[k];
      @ loop invariant \forall integer k; 0 <= k < i && is_even(arr[k]) == 0 ==>
      @   \forall integer j; 0 <= j < new_len && out[j] != arr[k];
      @ loop invariant new_len == (\numof(integer k; 0 <= k < i && is_even(arr[k]) == 1));
      @ loop assigns i, new_len, out[0..len-1]; // out[0..new_len-1] would be more precise if allowed
      @ loop variant len - i;
    */
    for (int i = 0; i < len; i++) {
        // Lambda function for even check is effectively inlined here
        // is_even(arr[i]) == 1 means arr[i] is even
        if (arr[i] % 2 == 0) {
            /*@ assert new_len < len; */ // Assert to ensure out[new_len] is a valid write
            out[new_len] = arr[i];
            new_len++;
        }
    }
    return new_len;
}
