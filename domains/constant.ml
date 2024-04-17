open Frontend
open Value_domain
open Frontend.Abstract_syntax_tree

module ConstantDomain : VALUE_DOMAIN = 
struct 
  (* type of abstract elements *)
  (* an element of type t abstracts a set of integers *)
  type t = | Top | Bot | Int of Z.t

  (* unrestricted value: [-oo,+oo] *)
  let top = Top

  (* bottom value: empty set *)
  let bottom = Bot

  (* constant: {c} *)
  let const c = Int c

  (* interval: [a,b] *)
  let rand a b = 
    if a < b then Top (* big abstraction *)
    else if a > b then Bot (* empty set *)
    else Int a (* singleton *)

  (* unary operation *)
  let unary value = function
  | AST_UNARY_PLUS -> value
  | AST_UNARY_MINUS -> match value with 
                       | Top | Bot -> value
                       | Int c -> Int (Z.neg c)

  (* binary operation *)
  let binary: t -> t -> int_binary_op -> t = failwith "unimplemented"


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
  let join: t -> t -> t = failwith "unimplemented"
  let meet: t -> t -> t = failwith "unimplemented"

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