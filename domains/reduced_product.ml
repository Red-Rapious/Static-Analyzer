open Frontend
open Abstract_syntax_tree

module ReducedProductDomain =
  struct
    module S = Signs.SignsDomain
    module C = Congruences.CongruencesDomain
    module I = Interval.IntervalDomain


    (* type of abstract elements *)
    (* an element of type t abstracts a set of integers *)
    (* we maintain information on three value domains at the same time *)
    (* note that the constants domain was not used since its expressivity 
       is included in the intervals domain *)
    type t = S.t * I.t * C.t

    (* unrestricted value: ℤ *)
    let top = S.top, I.top, C.top

    (* bottom value: empty set *)
    let bottom = S.bottom, I.bottom, C.bottom

    (* constant: {c} *)
    let const c = S.const c, I.const c, C.const c

    (* interval: [a,b] *)
    let rand a b = S.rand a b, I.rand a b, C.rand a b

    (* subset inclusion of concretizations *)
    let subset (xs, xi, xc) (ys, yi, yc) = S.subset xs ys && I.subset xi yi && C.subset xc yc

    (* gathers information from the three domains *)
    let rec reduction x =
      let (s, i, c) = match x with
      | _ -> x
      in
      let reduced = (S.meet s (I.to_sign i)), i, C.meet c (I.to_congruences i)
      in (*if subset x reduced then reduced else reduction reduced *)
      reduced

    (* unary operation *)
    let unary (s, i, c) op = reduction (S.unary s op, I.unary i op, C.unary c op)

    (* binary operation *)
    let binary (xs, xi, xc) (ys, yi, yc) op = reduction (S.binary xs ys op, I.binary xi yi op, C.binary xc yc op)

    (* comparison *)
    (* [compare x y op] returns (x',y') where
        - x' abstracts the set of v  in x such that v op v' is true for some v' in y
        - y' abstracts the set of v' in y such that v op v' is true for some v  in x
        i.e., we filter the abstract values x and y knowing that the test is true

        a safe, but not precise implementation, would be:
        compare x y op = (x,y)
      *)
    let rec compare (xs, xi, xc) (ys, yi, yc) op =
      let s1, s2 = S.compare xs ys op
      and i1, i2 = I.compare xi yi op
      and c1, c2 = C.compare xc yc op
      in reduction (s1, i1, c1), reduction (s2, i2, c2)

    (* set-theoretic operations *)
    let join (xs, xi, xc) (ys, yi, yc) = reduction (S.join xs ys, I.join xi yi, C.join xc yc)

    let meet (xs, xi, xc) (ys, yi, yc) = reduction (S.meet xs ys, I.meet xi yi, C.meet xc yc)

    (* backards unary operation *)
    (* [bwd_unary x op r] return x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x
     *)
    let bwd_unary (s, i, c) op (rs, ri, rc) = reduction (S.bwd_unary s op rs, I.bwd_unary i op ri, C.bwd_unary c op rc)

    (* backward binary operation *)
    (* [bwd_binary x y op r] returns (x',y') where
      - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
      - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
      i.e., we filter the abstract values x and y knowing that, after
      applying the operation op, the result is in r
    *)
    let bwd_binary (xs, xi, xc) (ys, yi, yc) op (rs, ri, rc)=
      let s1, s2 = S.bwd_binary xs ys op rs
      and i1, i2 = I.bwd_binary xi yi op ri
      and c1, c2 = C.bwd_binary xc yc op rc
      in reduction (s1, i1, c1), reduction (s2, i2, c2)


    (* widening *)
    let widen (xs, xi, xc) (ys, yi, yc) = reduction (S.widen xs ys, I.widen xi yi, C.widen xc yc)

    (* narrowing *)
    let narrow (xs, xi, xc) (ys, yi, yc) = reduction (S.narrow xs ys, I.narrow xi yi, C.narrow xc yc)

    (* check the emptiness of the concretization *)
    let is_bottom (s, i, c) = S.is_bottom s || I.is_bottom i || C.is_bottom c

    (* print abstract element *)
    let print fmt (s, i, c) = 
      Format.fprintf fmt "Product:@.  S: ";
      S.print fmt s;
      Format.fprintf fmt "  I: ";
      I.print fmt i;
      Format.fprintf fmt "  C: ";
      C.print fmt c
end
