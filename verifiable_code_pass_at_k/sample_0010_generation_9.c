// Task ID: 10
// Generation: 9

/*@ axiomatic SortedArray {
  @   logic boolean is_sorted{L}(int* a, integer from, integer to) reads a[from..to];
  @
  @   axiom is_sorted_empty{L}:
  @     \forall int* a, integer from, to; from >= to ==> is_sorted{L}(a, from, to);
  @
  @   axiom is_sorted_single{L}:
  @     \forall int* a, integer from; is_sorted{L}(a, from, from + 1);
  @
  @   axiom is_sorted_recursive{L}:
  @     \forall int* a, integer from, to;
  @       from < to - 1 ==> (is_sorted{L}(a, from, to) <==> (a[from] <= a[from+1] && is_sorted{L}(a, from + 1, to)));
  @ }
  @*/

/*@ axiomatic MinElement {
  @   logic boolean is_min_element{L}(int* arr, integer len, integer val);
  @
  @   axiom is_min_element_def{L}:
  @     \forall int* arr, integer len, val;
  @       is_min_element{L}(arr, len, val) <==> (\exists integer i; 0 <= i < len && arr[i] == val &&
  @                                              (\forall integer j; 0 <= j < len ==> arr[j] >= val));
  @
  @   // Helper axiom: If an element is the minimum and there are other elements, it must be less than or equal to them.
  @   axiom is_min_element_le{L}:
  @     \forall int* arr, integer len, val, k;
  @       is_min_element{L}(arr, len, val) && 0 <= k < len ==> val <= arr[k];
  @
  @   // Helper axiom: If all elements are greater than or equal to a value, and that value is in the array, it's the minimum.
  @   axiom is_min_element_found{L}:
  @     \forall int* arr, integer len, val;
  @       (\forall integer j; 0 <= j < len ==> arr[j] >= val) && (\exists integer i; 0 <= i < len && arr[i] == val) ==> is_min_element{L}(arr, len, val);
  @ }
  @*/

/*@
  @ requires \valid_read(arr + (0..len-1));
  @ requires len > 0;
  @ assigns \nothing;
  @
  @ ensures is_min_element{\old}(arr, len, \result);
  @ ensures \exists integer i; 0 <= i < len && arr[i] == \result;
  @
  @*/
int find_min(int* arr, int len) {
  int min_val = arr[0];
  /*@
    @ loop invariant 0 < i <= len;
    @ loop invariant \forall integer k; 0 <= k < i ==> min_val <= arr[k];
    @ loop invariant \exists integer k; 0 <= k < i && arr[k] == min_val;
    @ loop assigns i, min_val;
    @ loop variant len - i;
  */
  for (int i = 1; i < len; ++i) {
    if (arr[i] < min_val) {
      min_val = arr[i];
    }
  }
  return min_val;
}

/*@
  @ requires \valid(arr + (0..len-1));
  @ requires len > 0;
  @ requires 0 <= index < len;
  @ assigns arr[index];
  @
  @ behavior element_removed:
  @   assumes index < len - 1;
  @   ensures arr[len-1] == \old(arr[index]);
  @   ensures \forall integer k; 0 <= k < index ==> arr[k] == \old(arr[k]);
  @   ensures \forall integer k; index < k < len - 1 ==> arr[k] == \old(arr[k+1]);
  @
  @ behavior last_element:
  @   assumes index == len - 1;
  @   ensures \forall integer k; 0 <= k < len - 1 ==> arr[k] == \old(arr[k]);
  @
  @ complete behaviors element_removed, last_element;
  @ disjoint behaviors element_removed, last_element;
  @*/
void remove_at_index(int* arr, int len, int index) {
  if (index < len - 1) {
    arr[index] = arr[len - 1];
  }
}

/*@
  @ requires \valid_read(data + (0..data_len-1));
  @ requires \valid(n_smallest + (0..n-1));
  @ requires data_len >= 0;
  @ requires n >= 0;
  @ requires n <= data_len;
  @
  @ assigns n_smallest[0..n-1];
  @
  @ ensures is_sorted(n_smallest, 0, n);
  @ ensures \forall integer k; 0 <= k < n ==> (\exists integer i; 0 <= i < data_len && data[i] == n_smallest[k]);
  @ ensures (\forall integer k; 0 <= k < n ==> \forall integer j; 0 <= j < data_len && (\forall integer m; 0 <= m < n && n_smallest[m] != data[j]) ==> n_smallest[k] <= data[j]);
  @ ensures \forall integer k; 0 <= k < n - 1 ==> n_smallest[k] <= n_smallest[k+1];
  @*/
void get_n_smallest(int* data, int data_len, int* n_smallest, int n) {
  if (n == 0) {
    return;
  }

  // Create a mutable copy of the data
  /*@
    @ requires \valid(temp_data + (0..data_len-1));
    @ requires \valid_read(data + (0..data_len-1));
    @ requires data_len >= 0;
    @ assigns temp_data[0..data_len-1];
    @ ensures \forall integer k; 0 <= k < data_len ==> temp_data[k] == data[k];
  */
  int temp_data[data_len];
  /*@
    @ loop invariant 0 <= i <= data_len;
    @ loop invariant \forall integer k; 0 <= k < i ==> temp_data[k] == data[k];
    @ loop assigns i, temp_data[0..data_len-1];
    @ loop variant data_len - i;
  */
  for (int i = 0; i < data_len; ++i) {
    temp_data[i] = data[i];
  }

  int current_data_len = data_len;

  /*@
    @ loop invariant 0 <= i <= n;
    @ loop invariant current_data_len == data_len - i;
    @ loop invariant \forall integer k; 0 <= k < i ==> (\exists integer d_idx; 0 <= d_idx < data_len && n_smallest[k] == data[d_idx]);
    @ loop invariant \forall integer k; 0 <= k < i - 1 ==> n_smallest[k] <= n_smallest[k+1]; // Partial sort
    @ loop assigns i, n_smallest[0..n-1], temp_data[0..data_len-1], current_data_len;
    @ loop variant n - i;
  */
  for (int i = 0; i < n; ++i) {
    /*@
      @ requires current_data_len > 0;
      @ requires \valid_read(temp_data + (0..current_data_len-1));
      @ assigns \nothing;
      @ ensures is_min_element(temp_data, current_data_len, \result);
    */
    int min_val = find_min(temp_data, current_data_len);
    n_smallest[i] = min_val;

    // Find index of min_val in temp_data
    int min_idx = -1;
    /*@
      @ loop invariant 0 <= j <= current_data_len;
      @ loop invariant min_idx == -1 || (0 <= min_idx < j && temp_data[min_idx] == min_val);
      @ loop invariant \forall integer k; 0 <= k < j ==> temp_data[k] >= min_val;
      @ loop assigns j, min_idx;
      @ loop variant current_data_len - j;
    */
    for (int j = 0; j < current_data_len; ++j) {
      if (temp_data[j] == min_val) {
        min_idx = j;
        break;
      }
    }

    // Remove min_val from temp_data
    /*@
      @ requires \valid(temp_data + (0..current_data_len-1));
      @ requires current_data_len > 0;
      @ requires 0 <= min_idx < current_data_len;
      @ assigns temp_data[min_idx];
      @ assigns temp_data[current_data_len-1];
      @
      @ behavior element_removed:
      @   assumes min_idx < current_data_len - 1;
      @   ensures temp_data[current_data_len-1] == min_val;
      @   ensures \forall integer k; 0 <= k < min_idx ==> temp_data[k] == \old(temp_data[k]);
      @   ensures \forall integer k; min_idx < k < current_data_len - 1 ==> temp_data[k] == \old(temp_data[k+1]);
      @
      @ behavior last_element:
      @   assumes min_idx == current_data_len - 1;
      @   ensures \forall integer k; 0 <= k < current_data_len - 1 ==> temp_data[k] == \old(temp_data[k]);
      @
      @ complete behaviors element_removed, last_element;
      @ disjoint behaviors element_removed, last_element;
    */
    remove_at_index(temp_data, current_data_len, min_idx);
    current_data_len--;
  }

  // Sort the n_smallest array (selection sort logic)
  /*@
    @ loop invariant 0 <= i <= n;
    @ loop invariant is_sorted(n_smallest, 0, i);
    @ loop invariant \forall integer k; 0 <= k < i ==> (\forall integer l; i <= l < n ==> n_smallest[k] <= n_smallest[l]);
    @ loop assigns i, n_smallest[0..n-1];
    @ loop variant n - i;
  */
  for (int i = 0; i < n - 1; ++i) {
    int min_idx_in_smallest = i;
    /*@
      @ loop invariant i < j <= n;
      @ loop invariant i <= min_idx_in_smallest < j;
      @ loop invariant \forall integer k; i <= k < j ==> n_smallest[min_idx_in_smallest] <= n_smallest[k];
      @ loop assigns j, min_idx_in_smallest;
      @ loop variant n - j;
    */
    for (int j = i + 1; j < n; ++j) {
      if (n_smallest[j] < n_smallest[min_idx_in_smallest]) {
        min_idx_in_smallest = j;
      }
    }
    if (min_idx_in_smallest != i) {
      int temp = n_smallest[i];
      n_smallest[i] = n_smallest[min_idx_in_smallest];
      n_smallest[min_idx_in_smallest] = temp;
    }
  }
}
