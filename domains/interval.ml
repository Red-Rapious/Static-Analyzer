open Frontend
open Value_domain
open Frontend.Abstract_syntax_tree

type bound = | MinusInf | Finite of Z.t | PlusInf

let neg_bound = function
| MinusInf -> PlusInf
| Finite b -> Finite (Z.neg b)
| PlusInf -> MinusInf

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

let sub_bound x y =
  (*
    similarly, it is impossible to have (+oo) - (-oo) for the same reasons
  *)
  match x, y with
  | MinusInf, _ | _, PlusInf -> MinusInf
  | PlusInf, _ | _, MinusInf -> PlusInf
  | Finite x', Finite y' -> Finite (Z.sub x' y')

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

let [@warning "-8"] rec div_bound x y =
  match x, y with
  | _, (PlusInf|MinusInf) -> Finite Z.zero
  | _, Finite(z) when Z.equal z Z.zero -> failwith "interval.div_bound: division by zero"
  | PlusInf, Finite(z) when Z.gt z Z.zero -> PlusInf
  | PlusInf, Finite(z) when Z.lt z Z.zero -> MinusInf
  | MinusInf, Finite(z) when Z.gt z Z.zero -> PlusInf
  | MinusInf, Finite(z) when Z.lt z Z.zero -> PlusInf
  | Finite(x'), Finite(y') -> Finite (Z.div x' y')

let min_bound x y =
  match x, y with
  | MinusInf, _ | _, MinusInf -> MinusInf
  | _, PlusInf -> x
  | PlusInf, _ -> y
  | Finite(x'), Finite(y') -> Finite(Z.min x' y')

let max_bound x y =
  match x, y with
  | PlusInf, _ | _, PlusInf -> PlusInf
  | _, MinusInf -> x
  | MinusInf, _ -> y
  | Finite(x'), Finite(y') -> Finite(Z.max x' y')

module IntervalDomain : VALUE_DOMAIN = 
struct 
    (* type of abstract elements *)
    (* an element of type t abstracts a set of integers *)
    type t  = | Bot | Top | Interval of bound * bound

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
      | Interval(a, b), Interval(c, d) -> let lb = max_bound a c
                                          and rb = min_bound b d 
                                          in if lb > rb then Bot
                                             else if lb = MinusInf && rb = PlusInf then Top
                                             else Interval(lb, rb)

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
    let compare: t -> t -> compare_op -> (t * t) = failwith "unimplemented"


    (* backards unary operation *)
    (* [bwd_unary x op r] return x':
       - x' abstracts the set of v in x such as op v is in r
       i.e., we fiter the abstract values x knowing the result r of applying
       the operation on x
     *)
    let bwd_unary: t -> int_unary_op -> t -> t = failwith "unimplemented"

     (* backward binary operation *)
     (* [bwd_binary x y op r] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
       - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
       i.e., we filter the abstract values x and y knowing that, after
       applying the operation op, the result is in r
      *)
    let bwd_binary: t -> t -> int_binary_op -> t -> (t * t) = failwith "unimplemented"


    (* set-theoretic operations *)
    let join x y =
      match x, y with
      | Top, _ | _, Top -> Top
      | Bot, _ -> y
      | _, Bot -> x
      | Interval(a, b), Interval(c, d) -> let lb = min_bound a c
                                          and rb = max_bound b d
                                          in if lb = MinusInf && rb = PlusInf then Top
                                             else Interval(lb, rb)

    (* widening *)
    let widen: t -> t -> t = failwith "unimplemented"

    (* narrowing *)
    let narrow: t -> t -> t = failwith "unimplemented"

    (* subset inclusion of concretizations *)
    let subset: t -> t -> bool = failwith "unimplemented"

    (* check the emptiness of the concretization *)
    let is_bottom: t -> bool = failwith "unimplemented"

    (* print abstract element *)
    let print: Format.formatter -> t -> unit = failwith "unimplemented"
end