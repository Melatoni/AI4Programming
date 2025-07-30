// Task ID: 40
// Generation: 5

/*@
  // Rule II.1: Define an axiomatic block for recursive logic if needed.
  // For this problem, a simple loop invariant should suffice.
  // We need to define constants for array dimensions as they are not part of C function signatures for 2D arrays.
*/

// Define maximum dimensions for the 2D array and the frequency array size.
// These are illustrative and should be chosen based on expected input scale.
#define MAX_ROWS 10
#define MAX_COLS 10
#define MAX_VAL  100 // Maximum possible value of an element + 1 (for array sizing)

/*@
  requires R > 0 && R <= MAX_ROWS;
  requires C > 0 && C <= MAX_COLS;
  requires MAX_VAL > 0; // The size of the frequencies array must be positive.

  // The matrix elements must be within the valid range for the frequencies array.
  // Rule II.5: Prevent runtime errors.
  requires \forall integer i, j; 0 <= i < R && 0 <= j < C ==> 0 <= matrix[i][j] < MAX_VAL;

  // The frequencies array must be large enough to store counts for all possible values.
  requires frequencies_size == MAX_VAL;

  // The function assigns to the frequencies array.
  assigns frequencies[0..frequencies_size-1];

  // Post-condition: Each element in frequencies array should contain the correct count.
  ensures \forall integer val; 0 <= val < frequencies_size ==>
    frequencies[val] == (\num_of integer i, j; 0 <= i < R && 0 <= j < C && matrix[i][j] == val);
*/
void count_frequencies(int matrix[MAX_ROWS][MAX_COLS], int R, int C, int frequencies[MAX_VAL], int frequencies_size) {
    /*@
      loop invariant 0 <= k <= frequencies_size;
      loop invariant \forall integer x; 0 <= x < k ==> frequencies[x] == 0;
      loop assigns k, frequencies[0..frequencies_size-1];
      loop variant frequencies_size - k;
    */
    // Initialize frequencies array to all zeros.
    for (int k = 0; k < frequencies_size; k++) {
        frequencies[k] = 0;
    }

    /*@
      loop invariant 0 <= i <= R;
      loop invariant \forall integer r, c; 0 <= r < i && 0 <= c < C ==>
        frequencies[matrix[r][c]] == (\num_of integer x, y; 0 <= x < r && 0 <= y < C && matrix[x][y] == matrix[r][c]) +
                                      (\num_of integer y; 0 <= y <= c && matrix[i][y] == matrix[r][c]) + 1; // This invariant is tricky. Let's simplify.
      loop invariant \forall integer val; 0 <= val < frequencies_size ==>
        frequencies[val] == (\num_of integer r_idx, c_idx; 0 <= r_idx < i && 0 <= c_idx < C && matrix[r_idx][c_idx] == val);
      loop assigns i, j, frequencies[0..frequencies_size-1];
      loop variant R - i;
    */
    for (int i = 0; i < R; i++) {
        /*@
          loop invariant 0 <= j <= C;
          loop invariant \forall integer val; 0 <= val < frequencies_size ==>
            frequencies[val] == (\num_of integer r_idx, c_idx; 0 <= r_idx < i && 0 <= c_idx < C && matrix[r_idx][c_idx] == val) +
                                  (\num_of integer c_idx; 0 <= c_idx < j && matrix[i][c_idx] == val);
          loop assigns j, frequencies[0..frequencies_size-1];
          loop variant C - j;
        */
        for (int j = 0; j < C; j++) {
            // Rule II.5: Ensure matrix[i][j] is within bounds before access.
            // This is handled by the initial `requires` clause: 0 <= matrix[i][j] < MAX_VAL.
            frequencies[matrix[i][j]]++;
        }
    }
}
