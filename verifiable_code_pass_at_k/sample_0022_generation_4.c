// Task ID: 22
// Generation: 4

/*@
  requires N >= 0;
  requires \valid_read(arr + (0..N-1));
  
  assigns \nothing;
  
  // Rule II.2: Recursive logic for "first duplicate" property.
  // This defines what it means for an element at index 'k' to be the first duplicate.
  // It means arr[k] appears at an earlier index 'j', AND
  // for all indices 'm' before 'k', arr[m] does not appear at an earlier index 'p'.
  axiomatic FirstDuplicate {
    logic integer first_duplicate_index(int* arr, int N, integer k);
    
    // Base case: No duplicate found yet for k=0
    axiom first_duplicate_index_base:
      \forall int* arr, int N;
        first_duplicate_index(arr, N, 0) == -1; // -1 indicates no duplicate at or before index 0
    
    // Recursive step:
    axiom first_duplicate_index_rec:
      \forall int* arr, int N, integer k;
        0 < k <= N ==>
        ( (\exists integer j; 0 <= j < k && arr[j] == arr[k])
          ? k // arr[k] is a duplicate
          : first_duplicate_index(arr, N, k-1) // otherwise, check for duplicate before k
        ) == first_duplicate_index(arr, N, k);
  }
  
  // Rule II.3: The ensures clause uses logical equivalence.
  // The function returns the index of the first duplicate.
  // If no duplicate is found, it returns -1.
  ensures (\exists integer k; 0 <= k < N && (\exists integer j; 0 <= j < k && arr[j] == arr[k]) &&
           (\forall integer m; 0 <= m < k ==> (\forall integer p; 0 <= p < m ==> arr[p] != arr[m])))
           <==> (result != -1);
  ensures (result != -1) ==> (0 <= result < N && (\exists integer j; 0 <= j < result && arr[j] == arr[result]));
  ensures (result != -1) ==> (\forall integer m; 0 <= m < result ==> (\forall integer p; 0 <= p < m ==> arr[p] != arr[m]));
  ensures (result == -1) ==> (\forall integer k; 0 <= k < N ==> (\forall integer j; 0 <= j < k ==> arr[j] != arr[k]));
*/
int find_first_duplicate(int* arr, int N) {
    /*@
      loop invariant 0 <= i <= N;
      loop invariant \forall integer k; 0 <= k < i ==> (\forall integer j; 0 <= j < k ==> arr[j] != arr[k]);
      loop assigns i;
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        /*@
          loop invariant 0 <= j <= i;
          loop invariant \forall integer k; 0 <= k < j ==> arr[k] != arr[i];
          loop assigns j;
          loop variant i - j;
        */
        for (int j = 0; j < i; j++) {
            if (arr[i] == arr[j]) {
                return i; // Found the first duplicate
            }
        }
    }
    return -1; // No duplicate found
}
