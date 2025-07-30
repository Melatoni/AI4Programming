// Task ID: 41
// Generation: 4

/*@ axiomatic LambdaEvenFilter {
  @   logic boolean is_even_lambda(int x) = (x % 2 == 0);
  @ }
*/

/*@
  requires N >= 0;
  // Rule II.5: Prevent potential overflow if src[i] are large and used in arithmetic.
  // Although not strictly necessary for this problem, it's good practice.
  // For this specific problem, there are no arithmetic operations on array elements
  // that would cause overflow, but it's a general principle.
  requires \forall integer k; 0 <= k < N ==> (src[k] >= -2147483648 && src[k] <= 2147483647);

  // The function does not modify the source array.
  assigns dest[0..N-1];

  // Rule II.3: The ensures clause uses the robust logical equivalence pattern.
  // It states that an element is in dest if and only if it was an even number
  // in src and appeared at an earlier or same index in dest as its original index in src.
  ensures \forall integer j; 0 <= j < \result ==>
              is_even_lambda(dest[j]) &&
              (\exists integer i; 0 <= i < N && dest[j] == src[i] &&
                                  (\forall integer k; 0 <= k < j ==> dest[k] != src[i]));

  // This ensures clause states that every even number from src appears exactly once in dest
  // in the order they appeared in src.
  ensures \forall integer i; 0 <= i < N ==>
              (is_even_lambda(src[i]) <==>
               (\exists integer j; 0 <= j < \result && dest[j] == src[i] &&
                                   (\forall integer k; 0 <= k < i && is_even_lambda(src[k]) ==>
                                                       (\exists integer l; 0 <= l < j && dest[l] == src[k])) &&
                                   (\forall integer k; i < k < N && is_even_lambda(src[k]) ==>
                                                       (\exists integer l; j < l < \result && dest[l] == src[k]))
               ));

  // The length of the result array is exactly the count of even numbers in src.
  ensures \result == \numof(integer i; 0 <= i < N && is_even_lambda(src[i]));
*/
int filter_even_numbers(int src[], int N, int dest[]) {
    int count = 0;
    /*@
      loop invariant 0 <= i <= N;
      loop invariant 0 <= count <= i;

      // All elements processed so far (src[0]...src[i-1]) that were even
      // are correctly placed in dest[0]...dest[count-1].
      loop invariant \forall integer k; 0 <= k < i ==>
          (is_even_lambda(src[k]) <==>
           (\exists integer l; 0 <= l < count && dest[l] == src[k] &&
                               (\forall integer m; 0 <= m < l && dest[m] != src[k])));

      // The elements currently in dest are all even and come from src.
      loop invariant \forall integer k; 0 <= k < count ==> is_even_lambda(dest[k]);
      loop invariant \forall integer k; 0 <= k < count ==> (\exists integer l; 0 <= l < i && dest[k] == src[l]);

      // The count reflects the number of even elements encountered so far.
      loop invariant count == \numof(integer k; 0 <= k < i && is_even_lambda(src[k]));

      loop assigns i, count, dest[0..N-1];
      loop variant N - i;
    */
    for (int i = 0; i < N; i++) {
        // Rule I.2: Using 0 for false, 1 for true.
        if (is_even_lambda(src[i])) { // This is equivalent to (src[i] % 2 == 0)
            dest[count] = src[i];
            count++;
        }
    }
    return count;
}
