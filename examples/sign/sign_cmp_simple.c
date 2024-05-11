/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

void main(){
  int i = 42;
  int j = -42;
  assert(i != 0); //@OK
  assert(j != 0); //@OK
  assert(i == j); //@KO
}
