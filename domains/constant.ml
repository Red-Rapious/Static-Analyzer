open Frontend
open Value_domain
open Frontend.Abstract_syntax_tree

module ConstantDomain : VALUE_DOMAIN = 
struct 
  (* type of abstract elements *)
  (** an element of type t abstracts a set of integers *)
  type t = 
  | Top 
  | Bot 
  | Int of Z.t

  (* unrestricted value: [-oo,+oo] *)
  let top = Top

  (* bottom value: empty set *)
  let bottom = Bot

  (* constant: {c} *)
  let const c = Int c

  (* interval: [a,b] *)
  let rand a b = 
    if      a < b then Top   (* big abstraction *)
    else if a > b then Bot   (* empty set *)
    else               Int a (* singleton *)

  (* unary operation *)
  let unary x = function
  | AST_UNARY_PLUS -> x
  | AST_UNARY_MINUS -> match x with 
                       | Top | Bot -> x
                       | Int x -> Int (Z.neg x)

  (** binary operation *)
  let rec binary x y op = match x, y, op with 
  | Bot, _, _ -> Bot
  | _, Bot, _ -> Bot
  (* the only case where <Top op t2> can have a definite value is when t2 = 0 and op = AST_MULTIPLY *)
  | Top, Int(z), AST_MULTIPLY when z = Z.zero -> Int(Z.zero)
  | Top, _, _ -> Top
  (* division by zero *)
  | _, Int(z), AST_DIVIDE when z = Z.zero -> Bot
  (*| _, Top, AST_DIVIDE -> Bot (* division by zero may occur *)*) (* TODO?? *)
  | _, Int(z), AST_MODULO when z = Z.zero -> Bot
  | _, Top, _ -> binary x y op
  (* basic cases *)
  | Int(a), Int(b), _ -> 
    let f = match op with
    | AST_PLUS     -> Z.(+)
    | AST_MINUS    -> Z.(-)
    | AST_MULTIPLY -> Z.( * )
    | AST_DIVIDE   -> Z.(/)
    | AST_MODULO   -> Z.(mod)
    in Int(f a b)

  (* set-theoretic operations *)
  let join x y = match x, y with 
  | Top, _ | _, Top -> Top
  | Bot, _ -> y
  | _, Bot -> x
  | Int(x'), Int(y') when x' = y' -> x
  | Int(_), Int(_) -> Top

  let meet x y = match x, y with
  | Top, _ -> y
  | _, Top -> x
  | Bot, _ | _, Bot -> Bot
  | Int(x'), Int(y') when x' = y' -> x
  | Int(_), Int(_) -> Bot

    
  (* comparison *)
  (** [compare x y op] returns (x',y') where
      - x' abstracts the set of v  in x such that v op v' is true for some v' in y
      - y' abstracts the set of v' in y such that v op v' is true for some v  in x
      i.e., we filter the abstract values x and y knowing that the test is true

      a safe, but not precise implementation, would be:
      compare x y op = (x,y)
  *)
  let compare x y = function
  | AST_EQUAL -> begin match x, y with
                       | Bot, _ | _, Bot -> (Bot, Bot)
                       | Int a, Int b when not (Z.equal a b) ->  (Bot, Bot)
                       | Int _, _ -> (x, x)
                       | _, Int _ -> (y, y)
                       | Top, Top -> (Top, Top)
                 end
  | AST_NOT_EQUAL -> begin match x, y with
                           | Top, Top -> (Top, Top)
                           | Bot, _ | _, Bot -> (Bot, Bot)
                           (* the best safe approximation of [-oo,+oo]\{i} that we have is [-oo,+oo], hence Top *)
                           | Top, Int(_) | Int(_), Top -> (x, y)
                           (* exactly what we don't want *)
                           | Int(x'), Int(y') when x' != y' -> (x, y)
                           | Int(_), Int(_) -> (Bot, Bot)
                     end
  | op -> let [@warning "-8"] comp = match op with 
                                     | AST_LESS -> Z.lt
                                     | AST_LESS_EQUAL -> Z.leq
                                     | AST_GREATER -> Z.gt
                                     | AST_GREATER_EQUAL -> Z.geq
    in begin match x, y with 
             | Top, Top -> (Top, Top)
             | Bot, _ | _, Bot -> (Bot, Bot)
             (* the best safe approximation of [i, +oo] and [-oo, i] that we have is [-oo,+oo], hence Top *)
             | Top, Int(_) | Int(_), Top -> (x, y)
             | Int(x'), Int(y') when comp x' y' -> (x, y)
             | Int(_), Int(_) -> (Bot, Bot)
       end


  (* backards unary operation *)
  (** [bwd_unary x op r] return x':
      - x' abstracts the set of v in x such as op v is in r
      i.e., we filter the abstract values x knowing the result r of applying
      the operation on x
  *)
  let bwd_unary x op r = meet x (unary r (ast_uop_inv op))

  (* backward binary operation *)
  (** [bwd_binary x y op r] returns (x',y') where
    - x' abstracts the set of v  in x such that v op v' is in r for some v' in y
    - y' abstracts the set of v' in y such that v op v' is in r for some v  in x
    i.e., we filter the abstract values x and y knowing that, after
    applying the operation op, the result is in r
  *)
  let bwd_binary x y op r = match op with 
  | AST_MODULO -> (x, y) (* meet x Top = x, and we can't invert modulo so we abstract the invert as Top *)
  | _ -> (meet x (binary r y (ast_bop_inv op)), meet y (binary r x (ast_bop_inv op)))


  (* widening *)
  let widen = join

  (* subset inclusion of concretizations *)
  let subset x y = match x, y with
  | Bot, _ -> true
  | _, Top -> true
  | Int(x'), Int(y') when x' = y' -> true
  | _ -> false

  (* narrowing *)
  let narrow x y = if subset x y then y else Bot

  (* check the emptiness of the concretization *)
  let is_bottom t = t = Bot

  (* print abstract element *)
  let print formatter t =
    Format.fprintf formatter "%s" begin
      match t with
      | Top    -> "⊤"
      | Bot    -> "⊥"
      | Int(i) -> Z.to_string i
    end
end