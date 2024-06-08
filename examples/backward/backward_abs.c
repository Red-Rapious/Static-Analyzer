/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 * 
 *                 Created by Antoine Groudiev
 *                  Inspired by Antoine Miné
 */

void main(){
    int x = rand(-10, 10);
    int z = 0;
    int y = 0;
    if (x==0) {
        z = 0;
    } else {
        y = x;
        if (y < 0) { y = -y; }
        z = x / y;
    }
    assert(x > 0); //@OK
}
