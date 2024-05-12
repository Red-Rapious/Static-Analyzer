/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

void main(){
  int i = 10;
  int j = 3;
  int x = i % j;
  assert(x == 1); //@OK
  assert(x == 0); //@KO
}
