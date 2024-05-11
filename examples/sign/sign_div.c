/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

void main(){
  int i = 20;
  int j = 10;
  int k = -10;
  assert(i/j > 0); //@OK
  assert(i/k < 0); //@OK
}
