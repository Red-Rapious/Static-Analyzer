/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

void main(){
  int i = 0;
  // note: if j could take the value 0, it would get abstracted
  // as Top (since it can be either null or strictly positive)
  // and the assertion would fail because of incompletness
  int j = rand(1, 10);
  int x = i * j;

  assert(x == 0); //@OK
}
