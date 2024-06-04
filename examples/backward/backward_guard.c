/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 */

void main(){
    int x = rand(1, 10);
    int x_deux = 2*x;
    if (x_deux >= 10)
    {
        assert(x >= 5); //@OK
    }
}
