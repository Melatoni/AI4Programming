// Task ID: 17
// Generation: 0

/*@
  requires side >= 0; // Side length cannot be negative.
  // Rule II.5: Prevent overflow for perimeter calculation.
  // Assuming int is 32-bit, INT_MAX is 2,147,483,647.
  // Max side = INT_MAX / 4 = 536,870,911.
  requires side <= 536870911;

  assigns \nothing;

  // Rule II.3: For a simple function, the ensures clause directly states the postcondition.
  ensures \result == 4 * side;
*/
int perimeter_of_square(int side) {
    return 4 * side;
}
