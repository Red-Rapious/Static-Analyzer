/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

// This test checks simple modulo

void main(){
  int i = 10;
  int j = 3;
  int x = i % j;
  assert(x == 0); //@KO
  assert(x == 1); //@OK
}
