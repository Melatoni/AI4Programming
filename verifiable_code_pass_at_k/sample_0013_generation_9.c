// Task ID: 13
// Generation: 9

/*@ axiomatic WordCount {
  @   logic integer get_count(int* dict_data, int word_idx);
  @   axiom get_count_def{L}(int* dict_data, int word_idx) = dict_data[word_idx];
  @
  @   // Rule II.2: Recursive logic for properties over sequences.
  @   // Checks if a given index 'idx' has the maximum count up to 'max_idx'.
  @   logic boolean is_max_count_up_to(int* dict_data, int idx, int max_idx);
  @   axiom is_max_count_up_to_base{L}(int* dict_data, int idx, int max_idx) =
  @     idx == max_idx ==> (\forall integer k; 0 <= k < max_idx ==> get_count(dict_data, idx) >= get_count(dict_data, k));
  @   axiom is_max_count_up_to_rec{L}(int* dict_data, int idx, int max_idx) =
  @     idx < max_idx ==> (is_max_count_up_to(dict_data, idx, max_idx - 1) && get_count(dict_data, idx) >= get_count(dict_data, max_idx));
  @
  @   // Rule II.2, II.2.1: Helper axiom for recursive logic.
  @   // Ensures that if a certain index 'max_idx' holds the max count up to itself,
  @   // and it is greater than or equal to 'current_idx', then 'max_idx' is the actual maximum.
  @   // This helps the prover relate the loop invariant to the postcondition.
  @   axiom max_count_helper{L}(int* dict_data, int current_idx, int max_idx, int num_words) =
  @     (0 <= current_idx < num_words && 0 <= max_idx < num_words &&
  @      get_count(dict_data, max_idx) >= get_count(dict_data, current_idx) &&
  @      is_max_count_up_to(dict_data, max_idx, current_idx))
  @     ==> (\forall integer k; 0 <= k <= current_idx ==> get_count(dict_data, max_idx) >= get_count(dict_data, k));
  @ }
  @*/

/*@
  @ requires num_words >= 0;
  @ requires \valid_read(dict_data + (0..num_words - 1));
  @ // Rule II.5: Prevent potential overflow if counts are very large and summed up, though not directly summed here.
  @ // Ensure all counts are non-negative.
  @ ensures \forall integer i; 0 <= i < num_words ==> get_count(dict_data, i) >= 0;
  @
  @ assigns \nothing;
  @
  @ // Rule II.3: Use logical equivalence for boolean-like return.
  @ // The function returns the index of a word that has the maximum count among all words.
  @ // If num_words is 0, it returns -1.
  @ ensures (num_words == 0) ==> (\result == -1);
  @ ensures (num_words > 0) ==> (
  @   0 <= \result < num_words &&
  @   (\forall integer k; 0 <= k < num_words ==> get_count(dict_data, \result) >= get_count(dict_data, k))
  @ );
  @*/
int find_most_common_word_idx(int* dict_data, int num_words) { // Rule I.2: Use int for return and parameters.
    if (num_words == 0) {
        return -1;
    }

    int max_count_idx = 0; // Rule I.2: Initialized to 0.

    /*@
      @ loop invariant 0 <= i <= num_words;
      @ loop invariant 0 <= max_count_idx < num_words;
      @ // Rule II.4: Invariant stating that max_count_idx holds the maximum count
      @ // among all words examined so far (from 0 up to i-1).
      @ loop invariant (\forall integer k; 0 <= k < i ==> get_count(dict_data, max_count_idx) >= get_count(dict_data, k));
      @ loop invariant is_max_count_up_to(dict_data, max_count_idx, i - 1);
      @
      @ loop assigns i, max_count_idx;
      @ loop variant num_words - i; // Rule II.4: Loop variant for termination.
    */
    for (int i = 1; i < num_words; i++) {
        /*@ assert 0 <= i < num_words; */
        /*@ assert 0 <= max_count_idx < num_words; */
        if (get_count(dict_data, i) > get_count(dict_data, max_count_idx)) {
            max_count_idx = i;
        }
    }

    return max_count_idx;
}
