open Frontend
open Abstract_syntax_tree

module SignsDomain : Value_domain.VALUE_DOMAIN =
  struct

    (* type of abstract elements *)
    (* an element of type t abstracts a set of integers *)
    (* The elements follow the lattice of signs:
     *
     *                        (⊤)
     *                      /  |  \
     *                    /    |    \
     *                  /      |      \
     *                (-)     (0)     (+)
     *                  \      |      /
     *                    \    |    /
     *                      \  |  /
     *                        (⊥)
     *
     *)
    type t = | Bot | Top | Pos | Neg | Null

    (* unrestricted value: [-oo,+oo] *)
    let top = Top

    (* bottom value: empty set *)
    let bottom = Bot

    (* constant: {c} *)
    let const c = if c > Z.zero then Pos else if c < Z.zero then Neg else Null

    (* interval: [a,b] *)
    let rand a b = if const a = const b then const a else Top

    (* unary operation *)
    let unary x = function
    | AST_UNARY_PLUS -> x
    | AST_UNARY_MINUS -> match x with
                         | Top | Bot | Null -> x
                         | Pos -> Neg
                         | Neg -> Pos

    (* binary operation *)
    let binary x y = function
    | AST_PLUS -> begin match x, y with
                        | Pos, Pos -> Pos
                        | Neg, Neg -> Neg
                        | Null, Null -> Null
                        | Pos, Null | Null, Pos -> Pos
                        | Neg, Null | Null, Neg -> Neg
                        | Bot, _ | _, Bot -> Bot
                        | Top, _ | _, Top | Pos, Neg | Neg, Pos -> Top 
                  end
    | AST_MINUS -> begin match x, y with
                      | Pos, Neg -> Pos
                      | Neg, Pos -> Neg
                      | Null, Null -> Null
                      | Pos, Null | Null, Pos -> Pos
                      | Neg, Null | Null, Neg -> Neg
                      | Bot, _ | _, Bot -> Bot
                      | Top, _ | _, Top | Pos, Pos | Neg, Neg -> Top 
                  end
    | AST_MULTIPLY -> begin match x, y with
                            | Pos, Pos | Neg, Neg -> Pos
                            | Neg, Pos | Pos, Neg -> Neg
                            | (Pos|Neg|Null), Null | Null, (Pos|Neg)-> Null
                            | Bot, _ | _, Bot -> Bot
                            | Top, _ | _, Top -> Top
                      end
    | AST_DIVIDE -> begin match x, y with
                          | Pos, Pos | Neg, Neg -> Pos
                          | Neg, Pos | Pos, Neg -> Neg
                          | (Pos|Neg|Null), Null -> Bot (* division by zero *)
                          | Null, (Pos|Neg)-> Null
                          | Bot, _ | _, Bot -> Bot
                          | Top, _ | _, Top -> Top
                      end
    | AST_MODULO -> begin match x, y with
                      (* the result can always be zero, so we do not need to worry about the sign *)
                      (* things would have been more complex using an extended signs lattice *)
                      | (Pos|Neg), (Pos|Neg)-> Top
                      | (Pos|Neg|Null), Null -> Bot (* modulo by zero *)
                      | Null, (Pos|Neg)-> Null
                      | Bot, _ | _, Bot -> Bot
                      | Top, _ | _, Top -> Top
                  end


    (* comparison *)
    (* [compare x y op] returns (x',y') where
       - x' abstracts the set of v  in x such that v op v' is true for some v' in y
       - y' abstracts the set of v' in y such that v op v' is true for some v  in x
       i.e., we filter the abstract values x and y knowing that the test is true

       a safe, but not precise implementation, would be:
       compare x y op = (x,y)
     *)
     let rec compare x y op = match op with
     | AST_EQUAL -> begin match x, y with
                          | _, Top -> x, x
                          | Top, _  -> y, y
                          | Null, Null | Pos, Pos | Neg, Neg -> x, y
                          | _, _ -> (Bot, Bot)
                    end
     | AST_NOT_EQUAL -> begin match x, y with
                              | Top, Top -> Top, Top
                              | Bot, _ | _, Bot -> Bot, Bot
                              | Null, Null | Pos, Pos | Neg, Neg -> Bot, Bot
                              | _, _ -> x, y
                        end
     | AST_LESS -> begin match x, y with
                         | Top, Top -> Top, Top
                         | Null, Neg | Pos, Neg | Pos, Null
                         | Null, Null | Pos, Pos | Neg, Neg -> Bot, Bot
                         | _, _ -> x, y
                   end
     | AST_LESS_EQUAL -> begin match x, y with
                               | Top, Top -> Top, Top
                               | Null, Neg | Pos, Neg | Pos, Null-> Bot, Bot
                               | _, _ -> x, y
                         end
     | AST_GREATER -> let (x', y') = compare y x AST_LESS in y', x'
     | AST_GREATER_EQUAL -> let (x', y') = compare y x AST_LESS_EQUAL in y', x'


    (* set-theoretic operations *)
    let join x y = match x, y with
                   | _, Bot -> x
                   | Bot, _ -> y
                   | x, y when x = y -> x
                   | _ -> Top

    let meet x y = match x, y with
                  | _, Top -> x
                  | Top, _ -> y
                  | x, y when x = y -> x
                  | _ -> Bot

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
    let bwd_binary x y op r = x, y


    (* widening *)
    let widen x y = x

    (* narrowing *)
    let narrow x y = failwith "unimplemented"

    (* subset inclusion of concretizations *)
    let subset x y = match x, y with
    | Bot, _ -> true
    | _, Top -> true
    | _ -> false

    (* check the emptiness of the concretization *)
    let is_bottom x = x = Bot

    (* print abstract element *)
    let print fmt x = 
      Format.fprintf fmt "%s@." begin 
        match x with
        | Bot -> "(⊥)"
        | Top -> "(⊤)"
        | Null -> "(0)"
        | Pos -> "(+)"
        | Neg -> "(-)"
      end

end
