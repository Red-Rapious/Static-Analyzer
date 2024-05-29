open Frontend
open Abstract_syntax_tree

module CongruencesDomain = struct
  (* type of abstract elements *)
  (* an element of type t abstracts a set of integers *)
  (* an abstract element is either the empty set (Bot) or the set of
   * the elements of the form a*n+b for n in Z
   * note that Top is represented by 1*n+0 for n in Z
   *)
  type t = Bot | Modulo of Z.t * Z.t

  (* unrestricted value: ℤ *)
  let top = Modulo (Z.one, Z.zero)

  (* bottom value: empty set *)
  let bottom = Bot

  (* constant: {c} *)
  let const c = Modulo (Z.zero, c)

  (* interval: [a,b] *)
  let rand a b = if a = b then const a else top

  (* unary operation *)
  let unary x = function
    | AST_UNARY_PLUS -> x
    | AST_UNARY_MINUS -> (
        match x with Bot -> Bot | Modulo (a, b) -> Modulo (a, Z.neg b))

  (* binary operation *)
  let binary x y op =
    match (x, y) with
    | Bot, _ | _, Bot -> Bot
    | Modulo (a1, b1), Modulo (a2, b2) -> (
        match op with
        | AST_PLUS -> Modulo (Z.gcd a1 a2, Z.add b1 b2)
        | AST_MINUS -> Modulo (Z.gcd a1 a2, Z.sub b1 b2)
        | AST_MULTIPLY ->
            Modulo
              ( Z.gcd (Z.mul a1 a2) (Z.gcd (Z.mul a2 b1) (Z.mul a1 b2)),
                Z.mul b1 b2 )
        | AST_DIVIDE when a2 = Z.zero ->
            if b2 = Z.zero then Bot (* division by zero *)
            else if a1 = Z.zero then Modulo (Z.zero, Z.div b1 b2)
              (* constant divided by a constant *)
            else if b2 <= Z.gcd a1 b1 then Modulo (Z.div a1 b2, Z.div a1 b2)
            else top
        | AST_DIVIDE -> top
        | AST_MODULO when (a2, b2) = (Z.zero, Z.zero) ->
            Bot (* division by zero *)
        | AST_MODULO when a1 = Z.zero && a2 = Z.zero ->
            Modulo (Z.zero, Z.( mod ) b1 b2)
        | AST_MODULO when a2 = Z.zero && b2 <= a1 ->
            Modulo (Z.zero, Z.( mod ) b1 b2)
        | AST_MODULO when a2 = Z.zero ->
            Modulo (Z.gcd a1 (Z.gcd a2 b2), b1)
            (* avoid division by zero error *)
        | AST_MODULO
          when a1 = Z.zero
               && b1
                  < Z.max (Z.abs (Z.sub a2 (Z.( mod ) b2 a2))) (Z.( mod ) b2 a2)
          ->
            Modulo (a1, b1)
        | AST_MODULO -> Modulo (Z.gcd a1 (Z.gcd a2 b2), b1))

  (* comparison *)
  (* [compare x y op] returns (x',y') where
      - x' abstracts the set of v  in x such that v op v' is true for some v' in y
      - y' abstracts the set of v' in y such that v op v' is true for some v  in x
      i.e., we filter the abstract values x and y knowing that the test is true

      a safe, but not precise implementation, would be:
      compare x y op = (x,y)
  *)
  let rec compare x y op =
    match (x, y) with
    (* congruences performs poorly for comparaison *)
    (* the only interesting case is the case with two constants *)
    | Modulo (z, b1), Modulo (z', b2) when z = Z.zero && z' = Z.zero -> (
        match op with
        | AST_EQUAL -> if b1 = b2 then (x, y) else (Bot, Bot)
        | AST_NOT_EQUAL -> if b1 != b2 then (x, y) else (Bot, Bot)
        | AST_GREATER -> if b1 > b2 then (x, y) else (Bot, Bot)
        | AST_GREATER_EQUAL -> if b1 >= b2 then (x, y) else (Bot, Bot)
        | AST_LESS -> if b1 < b2 then (x, y) else (Bot, Bot)
        | AST_LESS_EQUAL -> if b1 <= b2 then (x, y) else (Bot, Bot))
    | _ -> (x, y)

  (* set-theoretic operations *)
  let join x y =
    match (x, y) with
    | _, Bot -> x
    | Bot, _ -> y
    | Modulo (a1, b1), Modulo (a2, b2) ->
        Modulo (Z.gcd (Z.gcd a1 a2) (Z.sub b1 b2), b1)

  let meet x y =
    match (x, y) with
    | _, Bot | Bot, _ -> Bot
    | Modulo (a1, b1), Modulo (a2, b2) ->
        let g, s, _ = Z.gcdext a1 a2 in
        if not (Z.congruent b1 b1 g) then Bot
        else if g = Z.zero then Modulo (Z.zero, b1)
        else
          Modulo
            (Z.lcm a1 a2, Z.add (Z.mul (Z.sub b2 b1) (Z.mul s (Z.div a1 g))) b1)

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
  let bwd_binary x y op r = (x, y)

  (* widening *)
  let widen = join

  (* narrowing *)
  let narrow x y = failwith "unimplemented"

  (* subset inclusion of concretizations *)
  let subset x y =
    match (x, y) with
    | Bot, _ -> true
    | _, Bot -> false
    | Modulo (a1, b1), Modulo (a2, b2) -> a1 <= a2 && Z.congruent b1 b2 a2

  (* check the emptiness of the concretization *)
  let is_bottom x = x = Bot

  (* print abstract element *)
  let print fmt x =
    match x with
    | Bot -> Format.fprintf fmt "⊥@."
    | Modulo (a, b) ->
        Format.fprintf fmt "{ %s·n+%s | n∈ℤ }@." (Z.to_string a) (Z.to_string b)
end
