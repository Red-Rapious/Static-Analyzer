/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

// This important test checks whether the property "is a multiple of" is
// verifiable using the congruence domain

// This example is especially interesting since the constants domain
// fails on it, while the congruences domain succeeds.

void main(){
  int i = rand(1, 10); // abstracted as Top = { 1*n+0 | n }
  int j = 3;
  int x = i * j;
  assert(x % 3 == 0); //@OK
  assert(x % 4 == 0); //@KO
}
