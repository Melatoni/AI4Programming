// Task ID: 2
// Generation: 9

/*@
  // Rule II.1, II.2: Define a recursive logic function to check if an element exists in a tuple list.
  axiomatic TupleListLogic {
    logic boolean exists_in_tuple_list(int val, int* arr, int len);

    axiom exists_in_tuple_list_base:
      \forall int val, int* arr;
        exists_in_tuple_list(val, arr, 0) == \false;

    axiom exists_in_tuple_list_recursive:
      \forall int val, int* arr, int len;
        len > 0 ==> exists_in_tuple_list(val, arr, len) == (arr[len - 1] == val || exists_in_tuple_list(val, arr, len - 1));

    // Rule II.2: Helper axiom to prove that if an element exists, its index is within bounds.
    axiom exists_in_tuple_list_helper_index:
      \forall int val, int* arr, int len;
        exists_in_tuple_list(val, arr, len) ==> \exists integer i; 0 <= i < len && arr[i] == val;
  }
*/

/*@
  requires \valid_read(list1 + (0..len1-1));
  requires \valid_read(list2 + (0..len2-1));
  requires len1 >= 0;
  requires len2 >= 0;
  requires \valid(result_list + (0..max_result_len-1));
  requires max_result_len >= 0;

  // Rule II.5: Prevent potential overflow if len1 or len2 are very large, though not strictly needed here.
  // This is a placeholder for general practice.
  requires len1 < INT_MAX / sizeof(int);
  requires len2 < INT_MAX / sizeof(int);

  assigns result_list[0..max_result_len-1];

  // Rule II.3: Use logical equivalence for boolean-like return value.
  ensures \result >= 0 && \result <= max_result_len;
  ensures \forall integer i; 0 <= i < \result ==>
              exists_in_tuple_list(result_list[i], list1, len1) &&
              exists_in_tuple_list(result_list[i], list2, len2);
  // Ensure no duplicates in the result list
  ensures \forall integer i, j; 0 <= i < \result && 0 <= j < \result && i != j ==> result_list[i] != result_list[j];
  // Ensure all common elements are found
  ensures \forall integer v;
              (exists_in_tuple_list(v, list1, len1) && exists_in_tuple_list(v, list2, len2)) ==>
              exists_in_tuple_list(v, result_list, \result);
*/
int find_similar_elements(int* list1, int len1, int* list2, int len2, int* result_list, int max_result_len) {
    int count = 0;

    /*@
      loop invariant 0 <= i <= len1;
      loop invariant 0 <= count <= max_result_len;
      loop invariant \forall integer k; 0 <= k < i ==>
          (exists_in_tuple_list(list1[k], list2, len2) ==> exists_in_tuple_list(list1[k], result_list, count)) &&
          (!exists_in_tuple_list(list1[k], result_list, count) ==>
              !exists_in_tuple_list(list1[k], list2, len2) ||
              !exists_in_tuple_list(list1[k], result_list, count-1)); // If not added, it must not be in list2 or already present
      loop invariant \forall integer k1, k2; 0 <= k1 < count && 0 <= k2 < count && k1 != k2 ==> result_list[k1] != result_list[k2];
      loop invariant \forall integer k; 0 <= k < count ==>
          exists_in_tuple_list(result_list[k], list1, i) && exists_in_tuple_list(result_list[k], list2, len2);
      loop assigns i, count, result_list[0..max_result_len-1];
      loop variant len1 - i;
    */
    for (int i = 0; i < len1; i++) {
        int element = list1[i];
        int found_in_list2 = 0; // Rule I.2: Use int for boolean

        /*@
          loop invariant 0 <= j <= len2;
          loop invariant found_in_list2 == 0 ==> \forall integer k; 0 <= k < j ==> list2[k] != element;
          loop invariant found_in_list2 == 1 ==> \exists integer k; 0 <= k < j && list2[k] == element;
          loop assigns j, found_in_list2;
          loop variant len2 - j;
        */
        for (int j = 0; j < len2; j++) {
            if (list2[j] == element) {
                found_in_list2 = 1;
                break;
            }
        }

        if (found_in_list2) {
            // Check if element is already in result_list
            int already_added = 0; // Rule I.2: Use int for boolean

            /*@
              loop invariant 0 <= k <= count;
              loop invariant already_added == 0 ==> \forall integer m; 0 <= m < k ==> result_list[m] != element;
              loop invariant already_added == 1 ==> \exists integer m; 0 <= m < k && result_list[m] == element;
              loop assigns k, already_added;
              loop variant count - k;
            */
            for (int k = 0; k < count; k++) {
                if (result_list[k] == element) {
                    already_added = 1;
                    break;
                }
            }

            if (!already_added) {
                if (count < max_result_len) {
                    result_list[count] = element;
                    count++;
                }
            }
        }
    }

    return count;
}
