/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

// This example is especially interesting since the constants domain
// fails on it, while the congruences domain succeeds.

void main(){
  int i = rand(1, 10); // abstracted as Top = { 1*n+0 | n }
  int j = i * 12;
  int x = j / 4;
  assert(x % 3 == 0); //@OK
  assert(x % 4 == 0); //@KO
}
