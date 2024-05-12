/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

// This test checks whether the rest of an euclidian division is always
// reduced between 0 and q-1, where q is the quotient

// This example is especially interesting since the constants domain
// fails on it, while the congruences domain succeeds.

void main(){
  int r = rand(1, 10); // abstracted as Top = { 1*n+0 | n }

  int i = 3 * r + 1;
  int j = 6 * r + 1;
  int k = 9 * r + 1;
  assert((i+j+k) % 3 == 0); //@OK
  assert((i+j+k) % 3 == 3); //@KO
}
