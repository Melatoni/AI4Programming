// Task ID: 40
// Generation: 4

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
*/

/*@
  // Rule II.1: Define an axiomatic block for recursive logic.
  axiomatic ListProperties {
    logic integer list_length{L}(int* list, integer start, integer end);
    axiom list_length_empty{L}:
      orall int* list, integer start, end;
      start >= end ==> list_length(list, start, end) == 0;
    axiom list_length_non_empty{L}:
      orall int* list, integer start, end;
      start < end ==> list_length(list, start, end) == 1 + list_length(list, start + 1, end);

    logic integer count_element{L}(int* list, integer start, integer end, int element);
    axiom count_element_empty{L}:
      orall int* list, integer start, end, int element;
      start >= end ==> count_element(list, start, end, element) == 0;
    axiom count_element_non_empty{L}:
      orall int* list, integer start, end, int element;
      start < end ==> count_element(list, start, end, element) ==
                      (if list[start] == element then 1 else 0) + count_element(list, start + 1, end, element);

    // Rule II.2: Helper axiom for count_element.
    axiom count_element_non_negative{L}:
      orall int* list, integer start, end, int element;
      count_element(list, start, end, element) >= 0;
  }
*/

/*@
  // Function: find_frequency
  // This function calculates the frequency of each unique element in a given list of lists.
  // It takes a 2D array (list of lists), its dimensions, a 1D array to store unique elements,
  // and a 1D array to store their corresponding frequencies.
  // The function returns the number of unique elements found.

  // Parameters:
  // - `lists`: The 2D array (list of lists).
  //   Rule I.3: Array pointer decay - `int (*lists)[max_col]`
  // - `rows`: Number of rows in `lists`.
  // - `cols`: Number of columns in `lists`.
  // - `unique_elements`: Output array to store unique elements.
  //   Rule I.3: Array pointer decay - `int* unique_elements`
  // - `frequencies`: Output array to store frequencies of unique elements.
  //   Rule I.3: Array pointer decay - `int* frequencies`
  // - `max_unique_capacity`: Maximum capacity of `unique_elements` and `frequencies` arrays.

  requires rows >= 0;
  requires cols >= 0;
  requires max_unique_capacity >= 0;

  // Ensure output arrays have enough capacity if there are elements.
  requires (rows * cols == 0) || (max_unique_capacity >= 1);

  // Pointers must be valid if dimensions are non-zero.
  requires (rows > 0 && cols > 0) ==> \valid_read(lists[0] + (0..(rows * cols - 1)));
  requires \valid(unique_elements + (0..max_unique_capacity - 1));
  requires \valid(frequencies + (0..max_unique_capacity - 1));

  assigns unique_elements[0..max_unique_capacity - 1],
          frequencies[0..max_unique_capacity - 1];

  ensures \result >= 0 && \result <= max_unique_capacity;
  ensures \result <= rows * cols; // Number of unique elements cannot exceed total elements.

  // Post-conditions for the unique_elements and frequencies arrays
  ensures orall integer i; 0 <= i < \result ==>
    // Each unique element appeared at least once.
    (\exists integer r, c; 0 <= r < rows && 0 <= c < cols && lists[r][c] == unique_elements[i]);

  ensures orall integer i; 0 <= i < \result ==>
    // Frequency matches the count of the element in the original lists.
    frequencies[i] == (\sum integer r, c; 0 <= r < rows && 0 <= c < cols && lists[r][c] == unique_elements[i]);

  ensures orall integer i, j; 0 <= i < \result && 0 <= j < \result && i != j ==>
    // All unique elements are distinct.
    unique_elements[i] != unique_elements[j];

  ensures orall integer r, c; 0 <= r < rows && 0 <= c < cols ==>
    // Every element in the input lists is accounted for in unique_elements.
    (\exists integer i; 0 <= i < \result && lists[r][c] == unique_elements[i]);
*/
int find_frequency(int (*lists)[100], int rows, int cols,
                   int* unique_elements, int* frequencies, int max_unique_capacity) {
    int unique_count = 0;

    /*@
      loop invariant 0 <= r <= rows;
      loop invariant orall integer i; 0 <= i < unique_count ==>
        // unique_elements[i] is truly unique among elements processed so far.
        (\forall integer j; 0 <= j < i ==> unique_elements[i] != unique_elements[j]);
      loop invariant orall integer i; 0 <= i < unique_count ==>
        // frequencies[i] stores the correct count for unique_elements[i] from already processed elements.
        frequencies[i] == (\sum integer r_prev, c_prev; 0 <= r_prev < r && 0 <= c_prev < cols && lists[r_prev][c_prev] == unique_elements[i]);
      loop invariant orall integer r_prev, c_prev; 0 <= r_prev < r && 0 <= c_prev < cols ==>
        // All elements processed so far are in unique_elements.
        (\exists integer i; 0 <= i < unique_count && lists[r_prev][c_prev] == unique_elements[i]);
      loop invariant unique_count <= max_unique_capacity;
      loop invariant unique_count >= 0;
      loop assigns r, c, unique_count, unique_elements[0..max_unique_capacity-1], frequencies[0..max_unique_capacity-1];
      loop variant rows - r;
    */
    for (int r = 0; r < rows; r++) {
        /*@
          loop invariant 0 <= c <= cols;
          loop invariant orall integer i; 0 <= i < unique_count ==>
            // unique_elements[i] is truly unique among elements processed so far.
            (\forall integer j; 0 <= j < i ==> unique_elements[i] != unique_elements[j]);
          loop invariant orall integer i; 0 <= i < unique_count ==>
            // frequencies[i] stores the correct count for unique_elements[i] from already processed elements (including current row up to c).
            frequencies[i] == (\sum integer r_prev; 0 <= r_prev < r && 0 <= c_prev < cols && lists[r_prev][c_prev] == unique_elements[i]) +
                              (\sum integer c_prev; 0 <= c_prev < c && lists[r][c_prev] == unique_elements[i]);
          loop invariant orall integer r_prev; 0 <= r_prev < r ==>
            (\forall integer c_prev; 0 <= c_prev < cols ==>
              (\exists integer i; 0 <= i < unique_count && lists[r_prev][c_prev] == unique_elements[i]));
          loop invariant orall integer c_prev; 0 <= c_prev < c ==>
            (\exists integer i; 0 <= i < unique_count && lists[r][c_prev] == unique_elements[i]);
          loop invariant unique_count <= max_unique_capacity;
          loop invariant unique_count >= 0;
          loop assigns c, unique_count, unique_elements[0..max_unique_capacity-1], frequencies[0..max_unique_capacity-1];
          loop variant cols - c;
        */
        for (int c = 0; c < cols; c++) {
            int element = lists[r][c];
            int found = 0; // Rule I.2: Use int for boolean.
            int found_idx = -1;

            /*@
              loop invariant 0 <= k <= unique_count;
              loop invariant orall integer i; 0 <= i < k ==> unique_elements[i] != element;
              loop invariant found == (if (\exists integer i; 0 <= i < k && unique_elements[i] == element) then 1 else 0);
              loop invariant found_idx == (if found == 1 then (\at(found_idx, LoopEntry)) else -1);
              loop invariant unique_count <= max_unique_capacity;
              loop assigns k, found, found_idx;
              loop variant unique_count - k;
            */
            for (int k = 0; k < unique_count; k++) {
                if (unique_elements[k] == element) {
                    found = 1; // Rule I.2: Use int for boolean.
                    found_idx = k;
                    break;
                }
            }

            // Rule II.5: Prevent potential write out of bounds.
            if (found == 0) { // Rule I.2: Use int for boolean.
                if (unique_count < max_unique_capacity) {
                    unique_elements[unique_count] = element;
                    frequencies[unique_count] = 1;
                    unique_count++;
                }
                // Else: Capacity exceeded, element not added.
            } else {
                // Rule II.5: Ensure found_idx is valid for access.
                // This is implicitly guaranteed by the loop invariant for 'found'.
                // If found is 1, found_idx must be between 0 and unique_count - 1.
                frequencies[found_idx]++;
            }
        }
    }

    return unique_count;
}
