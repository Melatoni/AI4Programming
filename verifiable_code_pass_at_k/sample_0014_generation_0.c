// Task ID: 14
// Generation: 0

/*@
  // Rule I.1: No standard libraries.
  // Rule I.2: Use int for booleans.
  // Rule I.3: Array pointer decay not applicable here.

  // Problem: Calculate the volume of a triangular prism.
  // Volume = (1/2 * base_triangle_base * base_triangle_height) * prism_length

  // We need to handle potential floating-point issues if we were to use doubles.
  // To keep it integer-only as per typical Frama-C/WP problems,
  // we will calculate 2 * Volume = base_triangle_base * base_triangle_height * prism_length.

  // We assume all dimensions are non-negative integers.
  // The result will be `2 * Volume`.

  // Rule II.5: Prevent Runtime Errors (RTE).
  // The maximum value for an `int` is `INT_MAX`.
  // We need to ensure that `base * height * length` does not overflow.
  // A safe upper bound for `int` (32-bit signed) is 2^31 - 1, which is approx 2 * 10^9.
  // If base, height, length are all up to 2000, then 2000^3 = 8 * 10^9, which overflows.
  // If they are all up to 1000, then 1000^3 = 1 * 10^9, which is fine.
  // Let's set a conservative upper bound for each dimension.
  // For example, if max_dim = 20000, then 20000 * 20000 * 20000 would overflow.
  // If max_dim = 2000, then 2000 * 2000 * 2000 = 8 * 10^9 (overflow for signed int).
  // If max_dim = 1290, then 1290*1290*1290 approx 2.14 * 10^9 (close to INT_MAX).
  // Let's require each dimension to be at most 1290 to prevent overflow of the product.
  requires base_triangle_base >= 0;
  requires base_triangle_height >= 0;
  requires prism_length >= 0;

  // The maximum value for an `int` is `INT_MAX`.
  // We need to ensure that `base_triangle_base * base_triangle_height` does not overflow
  // before multiplying by `prism_length`.
  // And then that `(base_triangle_base * base_triangle_height) * prism_length` does not overflow.

  // A more robust way to prevent overflow is to state the product must be within `INT_MAX`.
  // However, WP might struggle to prove this without individual bounds.
  // Let's use individual bounds for `int` (32-bit signed).
  // Assuming `int` is 32-bit, `INT_MAX` is 2147483647.
  // The cube root of INT_MAX is approx 1290.
  requires base_triangle_base <= 1290;
  requires base_triangle_height <= 1290;
  requires prism_length <= 1290;

  assigns \nothing;

  // The function returns 2 * Volume.
  ensures \result == base_triangle_base * base_triangle_height * prism_length;
*/
int calculate_double_triangular_prism_volume(int base_triangle_base, int base_triangle_height, int prism_length) {
    // Volume = (1/2 * base * height) * length
    // To avoid floating point, we calculate 2 * Volume
    // 2 * Volume = base * height * length
    int result = base_triangle_base * base_triangle_height * prism_length;
    return result;
}
