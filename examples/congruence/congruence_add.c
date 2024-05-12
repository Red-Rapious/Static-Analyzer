/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

void main(){
  int i = 24;
  int j = 42;
  int x = i + j;
  assert(x == 67); //@KO
  assert(x == 66); //@OK
}
