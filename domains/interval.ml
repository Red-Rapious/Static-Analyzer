open Frontend
open Value_domain
open Frontend.Abstract_syntax_tree

let swap (x, y) = (y, x)

(* a custom type representing the bound of an interval *)
type bound = | MinusInf | Finite of Z.t | PlusInf

(* -- the following implements diverse operations over bounds -- *)

(** returns the opposite of a bound *)
let neg_bound = function
| MinusInf -> PlusInf
| Finite b -> Finite (Z.neg b)
| PlusInf -> MinusInf

(** adds two bounds *)
let add_bound x y =
  (* 
    note that by construction it is impossible to have +oo + -oo
    since -oo can only be left and +oo can only be right, and we
    only add bounds of the same side (left or right)
  *)
  match x, y with
  | MinusInf, _ | _, MinusInf -> MinusInf
  | PlusInf, _ | _, PlusInf -> PlusInf
  | Finite x', Finite y' -> Finite (Z.add x' y')

(** substracts two bounds *)
let sub_bound x y =
  (*
    similarly, it is impossible to have (+oo) - (-oo) for the same reasons
  *)
  match x, y with
  | MinusInf, _ | _, PlusInf -> MinusInf
  | PlusInf, _ | _, MinusInf -> PlusInf
  | Finite x', Finite y' -> Finite (Z.sub x' y')

(** multiplies two bounds *)
let rec mul_bound x y =
  match x, y with
  | MinusInf, PlusInf -> MinusInf
  | PlusInf, PlusInf | MinusInf, MinusInf -> PlusInf
  | _, Finite(z) when Z.equal z Z.zero -> Finite Z.zero
  | PlusInf, Finite(y') when Z.gt y' Z.zero -> PlusInf
  | PlusInf, Finite(y') when Z.lt y' Z.zero -> MinusInf
  | MinusInf, Finite(y') when Z.gt y' Z.zero -> MinusInf
  | MinusInf, Finite(y') when Z.lt y' Z.zero -> PlusInf
  | Finite(x'), Finite(y') -> Finite (Z.mul x' y')
  | _, _ -> mul_bound y x

(** divides two bounds *)
let [@warning "-8"] rec div_bound x y =
  match x, y with
  | _, (PlusInf|MinusInf) -> Finite Z.zero
  | _, Finite(z) when Z.equal z Z.zero -> failwith "interval.div_bound: division by zero"
  | PlusInf, Finite(z) when Z.gt z Z.zero -> PlusInf
  | PlusInf, Finite(z) when Z.lt z Z.zero -> MinusInf
  | MinusInf, Finite(z) when Z.gt z Z.zero -> PlusInf
  | MinusInf, Finite(z) when Z.lt z Z.zero -> PlusInf
  | Finite(x'), Finite(y') -> Finite (Z.div x' y')

(** takes the minimum of two bounds*)
let min_bound x y =
  match x, y with
  | MinusInf, _ | _, MinusInf -> MinusInf
  | _, PlusInf -> x
  | PlusInf, _ -> y
  | Finite(x'), Finite(y') -> Finite(Z.min x' y')

(** takes the maximum of two bounds *)
let max_bound x y =
  match x, y with
  | PlusInf, _ | _, PlusInf -> PlusInf
  | _, MinusInf -> x
  | MinusInf, _ -> y
  | Finite(x'), Finite(y') -> Finite(Z.max x' y')

(** check whether x >= y *)
let geq_bound x y =
  match x, y with
  | PlusInf, _ -> true
  | MinusInf, MinusInf -> true (* this case will never be called *)
  | MinusInf, _ -> false
  | Finite(x'), Finite(y') -> Z.geq x' y'
  | Finite(_), PlusInf -> false
  | Finite(_), MinusInf -> true

(** check whether x > y *)
let gt_bound x y =
  match x, y with
  | PlusInf, PlusInf -> false
  | PlusInf, _ -> true
  | MinusInf, _ -> false
  | Finite(x'), Finite(y') -> Z.gt x' y'
  | Finite(_), PlusInf -> false
  | Finite(_), MinusInf -> true

let bound_to_string = function
| MinusInf -> "-oo"
| Finite a -> Z.to_string a
| PlusInf -> "+oo"


module IntervalDomain : VALUE_DOMAIN = 
struct 
    (* type of abstract elements *)
    (* an element of type t abstracts a set of integers *)
    type t  = | Bot | Top | Interval of bound * bound

    (* print abstract element *)
    let print formatter = function
    | Top -> Format.fprintf formatter "⊤"
    | Bot -> Format.fprintf formatter "⊥"
    | Interval(a, b) -> Format.fprintf formatter "[%s, %s]" (bound_to_string a) (bound_to_string b)

    (** transforms an interval into Bot if the bounds are incorrect *)
    let bottomize_if_necessary = function
    | Interval(x, y) when gt_bound x y -> Bot
    | x -> x 

    (* unrestricted value: [-oo,+oo] *)
    (* note that we could have also chosen to represent Top by Interval(MinusInf, PlusInf) *)
    let top = Top

    (* bottom value: empty set *)
    let bottom = Bot

    (* constant: {c} *)
    let const c = Interval(Finite c, Finite c)

    (* interval: [a,b] *)
    let rand a b = Interval(Finite a, Finite b)


    (* unary operation *)
    let unary x = function
    | AST_UNARY_PLUS -> x
    | AST_UNARY_MINUS -> match x with
                         | Top | Bot -> x
                         | Interval (lb, rb) -> Interval(neg_bound rb, neg_bound lb)


    let meet x y =
      match x, y with
      | Bot, _ | _, Bot -> Bot
      | Top, _ -> y
      | _, Top -> x
      | Interval(a, b), Interval(c, d) -> bottomize_if_necessary (Interval(min_bound a c, max_bound b d))

    (* binary operation *)
    let binary x y op = 
      match x, y, op with
      | _, Top, _ -> Top
      | Top, _, _ -> Top
      | Bot, _, _ -> Bot
      | _, Bot, _ -> Bot
      | Interval(a, b), Interval(c, d), _ -> match op with
                                             | AST_PLUS     -> Interval(add_bound a c, add_bound b d)
                                             | AST_MINUS    -> Interval(sub_bound a d, sub_bound b c)
                                             | AST_MULTIPLY -> let b1 = mul_bound a c
                                                               and b2 = mul_bound a d
                                                               and b3 = mul_bound b c
                                                               and b4 = mul_bound b d
                                                               in let mini = min_bound (min_bound b1 b2) (min_bound b3 b4)
                                                                  and maxi = max_bound (max_bound b1 b2) (max_bound b3 b4)
                                                               in Interval(mini, maxi)
                                             | AST_MODULO   -> meet x y
                                             | AST_DIVIDE   -> let b1 = div_bound a c
                                                               and b2 = div_bound a d
                                                               and b3 = div_bound b c
                                                               and b4 = div_bound b d
                                                               in let mini = min_bound (min_bound b1 b2) (min_bound b3 b4)
                                                                  and maxi = max_bound (max_bound b1 b2) (max_bound b3 b4)
                                                               in Interval(mini, maxi)
                                             


    (* comparison *)
    (* [compare x y op] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is true for some v' in y
       - y' abstracts the set of v' in y such that v op v' is true for some v  in x
       i.e., we filter the abstract values x and y knowing that the test is true

       a safe, but not precise implementation, would be:
       compare x y op = (x,y)
     *)
     let mono_compare a b c d op =
      let lu, ru = match op with
      | AST_EQUAL -> max_bound a c, min_bound b d
      | AST_NOT_EQUAL ->
        if c = d && b = c then
          a, sub_bound b (Finite Z.one)
        else if c = d && d = a then
          add_bound a (Finite Z.one), b
        else
          a, b
      | AST_LESS -> a, min_bound b (sub_bound d (Finite Z.one))
      | AST_LESS_EQUAL -> a, min_bound b d
      | AST_GREATER -> max_bound a (add_bound c (Finite Z.one)), b
      | AST_GREATER_EQUAL -> max_bound a c, b
      in
      bottomize_if_necessary (Interval (lu, ru))
    
    let compare u v op =
      let res = 
      match (u, v) with
      | Interval (a, b), Interval (c, d) -> mono_compare a b c d op, 
                                            mono_compare c d a b (ast_cop_reverse op)
      | _ -> Bot, Bot
      in
      res
    (*let rec compare x y = function
    | AST_EQUAL -> let joint = meet x y in (joint, joint)
    | AST_NOT_EQUAL -> begin match x, y with
                             (* we still have no better approximation of [-oo, +oo]\{y} than [-oo, +oo] *)
                             | Top, _ -> (Top, y)
                             | _, Top -> (x, Top)
                             | Bot, _ | _, Bot -> (Bot, Bot)
                             | Interval(a, b), Interval(c, d) when a = c && b = d -> (Bot, Bot)
                             | Interval(_, _), Interval(_, _) -> (x, y)
                       end
    | AST_LESS -> begin match x, y with
                        | Top, Top -> (Top, Top)
                        | Bot, _ | _, Bot -> (Bot, Bot)
                        | Interval(_, b), Top -> (x, Interval(b, PlusInf))
                        | Top, Interval(c, _) -> (Interval(MinusInf, c), y)
                        | Interval(a, b), Interval(c, d) when geq_bound a d -> (Bot, Bot)
                        | Interval(a, b), Interval(c, d) -> 
                          (Interval(a, min_bound b (sub_bound d (Finite Z.one))), 
                           Interval(max_bound c (add_bound a (Finite Z.one)), d))
                  end
    (*| AST_LESS -> begin match x, y with
                        | Interval(a, b), Interval(c, d) -> Interval(a, min_bound b (sub_bound d (Finite Z.one))), Interval(c, max_bound d (add_bound b (Finite Z.one)))
                        | _ -> (Bot, Bot)
                  end*)
    | AST_LESS_EQUAL -> begin match x, y with
                              | Top, Top -> (Top, Top)
                              | Bot, _ | _, Bot -> (Bot, Bot)
                              | Interval(_, b), Top -> (x, Interval(b, PlusInf))
                              | Top, Interval(c, _) -> (Interval(MinusInf, c), y)
                              | Interval(a, b), Interval(c, d) when gt_bound a d -> (Bot, Bot)
                              | Interval(a, b), Interval(c, d) -> (Interval(a, min_bound b d), Interval(max_bound a c, d))
                        end
    (*| AST_LESS_EQUAL -> begin match x, y with
                        | Interval(a, b), Interval(c, d) -> Interval(a, min_bound b d), Interval(c, max_bound d b)
                        | _ -> (Bot, Bot)
                        end*)
    | AST_GREATER | AST_GREATER_EQUAL as op -> swap (compare y x (if op = AST_GREATER then AST_LESS else AST_LESS_EQUAL))*)

    (** TODO: used for debugging, check if improves things *)
    (*and compare x y op =
      let res = ccompare x y op in
      (*let res = (bottomize_if_necessary (fst res), bottomize_if_necessary (snd res)) in*)
      if !Options.verbose then begin
      Format.printf "compare " ;
      print Format.std_formatter x ;
      Format.printf " " ;
      print Format.std_formatter y ;
      Format.printf " %s  --->   " (Cfg_printer.string_of_compare_op op) ;
      Format.printf "(" ;
      print Format.std_formatter (fst res) ;
      Format.printf ", " ;
      print Format.std_formatter (snd res) ;
      Format.printf ")@." 
      end ;
      res*)

    (* backards unary operation *)
    (* [bwd_unary x op r] return x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x
     *)
    let bwd_unary x op r = meet x (unary r (ast_uop_inv op))

    (* backward binary operation *)
    (* [bwd_binary x y op r] returns (x',y') where
      - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
      - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
      i.e., we filter the abstract values x and y knowing that, after
      applying the operation op, the result is in r
    *)
    let bwd_binary x y op r = match op with 
    | AST_MODULO -> (x, y) (* meet x Top = x, and we can't invert modulo so we abstract the invert as Top *)
    | _ -> (meet x (binary r y (ast_bop_inv op)), meet y (binary r x (ast_bop_inv op)))


    let join x y =
      match x, y with
      | Top, _ | _, Top -> Top
      | Bot, _ -> y
      | _, Bot -> x
      | Interval(a, b), Interval(c, d) -> let lb = min_bound a c
                                          and rb = max_bound b d
                                          in if lb = MinusInf && rb = PlusInf then Top
                                             else Interval(lb, rb)

    (* narrowing *)
    let narrow x y = failwith "unimplemented"

    (* subset inclusion of concretizations *)
    let subset x y =
      match x, y with
      | _, Top -> true
      | Top, _ -> false
      | Bot, _ -> true
      | _, Bot -> false
      | Interval(a, b), Interval(c, d) -> geq_bound a c && geq_bound d b

    (* widening *)
    let widen x y =
      match x, y with
           | Top, _ | _, Top -> Top
           | Bot, _ -> y
           | _, Bot -> x
           | Interval(a, b), Interval(c, d) -> Interval((if gt_bound c a then a else MinusInf), 
                                                        (if gt_bound b d then b else PlusInf))

    (* check the emptiness of the concretization *)
    let is_bottom = function
    | Bot -> true
    (* if everything goes well, this case is never used, but who knows... *)
    | Interval(a, b) when a > b -> 
      Format.eprintf "[warning] interval.is_bottom: an interval with incorrect bounds has been detected\n" ;
      true
    | _ -> false

end