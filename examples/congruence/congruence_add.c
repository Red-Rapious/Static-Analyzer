/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

// This test checks whether the rest of the euclidian division
// behaves accordingly with addition

// This example is especially interesting since the constants domain
// fails on it, while the congruences domain succeeds.

void main(){
  int r1 = rand(1, 10); // abstracted as Top = { 1*n+0 | n }
  int r2 = rand(1, 10);

  int i = 3 * r1 + 1;
  int j = 3 * r2 + 1;
  assert((i+j) % 3 == 2); //@OK
  assert((i+j) % 3 == 0); //@KO
}
