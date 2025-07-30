// Task ID: 26
// Generation: 3

/*@
  // Rule II.1: Define recursive logic for properties over sequences.
  // This axiomatic block defines what it means for a tuple list to have 'all k elements'.
  // A tuple list `arr` of size `n` has `all k elements` if for every `i` from `0` to `n-1`,
  // the element `arr[i]` is between `0` and `k-1` (inclusive), and
  // for every value `j` from `0` to `k-1`, there exists at least one `i` such that `arr[i]` equals `j`.
  axiomatic AllKelements {
    logic boolean is_present_in_list(int val, int* arr, int n, int start_idx);

    // Base case: If start_idx reaches n, value is not found.
    axiom is_present_in_list_base:
      \forall int val, int* arr, int n;
        is_present_in_list(val, arr, n, n) == \false;

    // Recursive case: Check current element, then recurse.
    axiom is_present_in_list_rec:
      \forall int val, int* arr, int n, int start_idx;
        0 <= start_idx < n ==>
        is_present_in_list(val, arr, n, start_idx) == (arr[start_idx] == val || is_present_in_list(val, arr, n, start_idx + 1));

    logic boolean all_elements_present_recursive(int k, int* arr, int n, int current_k_val);

    // Base case: If current_k_val reaches k, all values from 0 to k-1 have been checked.
    axiom all_elements_present_recursive_base:
      \forall int k, int* arr, int n;
        current_k_val == k ==> all_elements_present_recursive(k, arr, n, current_k_val) == \true;

    // Recursive case: Check if current_k_val is present, then recurse for current_k_val + 1.
    axiom all_elements_present_recursive_rec:
      \forall int k, int* arr, int n, int current_k_val;
        0 <= current_k_val < k ==>
        all_elements_present_recursive(k, arr, n, current_k_val) == (is_present_in_list(current_k_val, arr, n, 0) && all_elements_present_recursive(k, arr, n, current_k_val + 1));

    predicate has_all_k_elements(int* arr, int n, int k) =
      (\forall integer i; 0 <= i < n ==> (0 <= arr[i] < k)) &&
      (k == 0 || all_elements_present_recursive(k, arr, n, 0)); // If k=0, no elements are required. If k > 0, all 0..k-1 must be present.
  }
*/

/*@
  requires n >= 0;
  requires k >= 0;
  // Rule II.5: Ensure array access is valid.
  requires \valid_read_array(arr, n);
  
  // Rule II.5: Prevent potential issues if k is very large, though not strictly needed for this logic.
  // For example, if k were used as an array index, this would be crucial.
  // Here, it limits the range of k for practical verification.
  requires k <= 10000; 

  assigns \nothing;

  // Rule II.3: Use logical equivalence for boolean-like return values.
  ensures has_all_k_elements(arr, n, k) <==> (\result == 1);
*/
int has_all_k_elements_in_tuple_list(int* arr, int n, int k) {
    if (k == 0) {
        return 1; // If k is 0, no elements are required, so it trivially has "all 0 elements".
    }

    // First, check if all elements in the array are within the range [0, k-1].
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> (0 <= arr[j] < k);
      loop assigns i;
      loop variant n - i;
    */
    for (int i = 0; i < n; ++i) {
        if (arr[i] < 0 || arr[i] >= k) {
            return 0;
        }
    }

    // If n is less than k, it's impossible to have all k distinct elements.
    // This optimization helps reduce proof complexity for the second loop.
    if (n < k) {
        return 0;
    }

    // Now, check if every value from 0 to k-1 is present in the array.
    /*@
      loop invariant 0 <= current_k_val <= k;
      // Invariant: All values from 0 to current_k_val - 1 have been found in the array.
      loop invariant \forall integer val_to_check; 0 <= val_to_check < current_k_val ==>
                       (\exists integer i; 0 <= i < n && arr[i] == val_to_check);
      loop assigns current_k_val;
      loop variant k - current_k_val;
    */
    for (int current_k_val = 0; current_k_val < k; ++current_k_val) {
        int found = 0; // Rule I.2: Use int for boolean
        /*@
          loop invariant 0 <= i <= n;
          // Invariant: If 'found' is 1, then arr[j] == current_k_val for some j < i.
          // If 'found' is 0, then arr[j] != current_k_val for all j < i.
          loop invariant (found == 1) ==> (\exists integer idx; 0 <= idx < i && arr[idx] == current_k_val);
          loop invariant (found == 0) ==> (\forall integer idx; 0 <= idx < i ==> arr[idx] != current_k_val);
          loop assigns i, found;
          loop variant n - i;
        */
        for (int i = 0; i < n; ++i) {
            if (arr[i] == current_k_val) {
                found = 1;
                break;
            }
        }
        if (found == 0) {
            return 0; // current_k_val was not found in the array.
        }
    }

    return 1; // All checks passed.
}
