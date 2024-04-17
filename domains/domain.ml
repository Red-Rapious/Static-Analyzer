(*
  Cours "Sémantique et Application à la Vérification de programmes"

  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)

open Frontend
open Frontend.Abstract_syntax_tree
open Domain
open Cfg
open Value_domain

(* Signature for the variables *)

module type VARS = sig
  val support: var list
end

(*
  Signature of abstract domains representing sets of envrionments
  (for instance: a map from variable to their bounds).
 *)

module type DOMAIN = functor (_:VALUE_DOMAIN) ->
  sig

    (* type of abstract elements *)
    (* an element of type t abstracts a set of mappings from variables
       to integers
     *)
    type t

    (* initial environment, with all variables initialized to 0 *)
    val init: t

    (* empty set of environments *)
    val bottom: t

    (* assign an integer expression to a variable *)
    val assign: t -> var -> int_expr -> t

    (* filter environments to keep only those satisfying the boolean expression *)
    val guard: t -> bool_expr -> t

    (* abstract join *)
    val join: t -> t -> t

    (* abstract meet *)
    val meet: t -> t -> t

    (* widening *)
    val widen: t -> t -> t

    (* narrowing *)
    val narrow: t -> t -> t

    (* whether an abstract element is included in another one *)
    val subset: t -> t -> bool

    (* whether the abstract element represents the empty set *)
    val is_bottom: t -> bool

    (* prints *)
    val print: Format.formatter -> t -> unit

  end

module VarMap = Map.Make(Var)

module Domain(Vars:VARS) : DOMAIN = functor (ValueDomain:VALUE_DOMAIN) ->
struct 
    (* type of abstract elements *)
    (* an element of type t abstracts a set of mappings from variables
       to integers
     *)
     type t = ValueDomain.t VarMap.t

     (* initial environment, with all variables initialized to 0 *)
      let init =
        List.fold_left (fun map var -> VarMap.add var (ValueDomain.const Z.zero) map) VarMap.empty Vars.support

 
     (* empty set of environments *)
     let bottom: t = VarMap.empty

    (* whether the abstract element represents the empty set *)
    let is_bottom: t -> bool = VarMap.is_empty

     let rec int_expr_to_value domain = function
      | CFG_int_const(i) -> 
        ValueDomain.const i
      | CFG_int_unary(op, expr) -> 
        ValueDomain.unary (int_expr_to_value domain expr) op
      | CFG_int_binary (op, e1, e2) ->
        ValueDomain.binary (int_expr_to_value domain e1) (int_expr_to_value domain e2) op
      | CFG_int_var(var) -> 
        VarMap.find var domain
      | CFG_int_rand(i1, i2) -> 
        ValueDomain.rand i1 i2
 
    (* assign an integer expression to a variable *)
    let assign  domain var int_expr = 
    VarMap.add var (int_expr_to_value domain int_expr) domain

    (* 
      backward domain analysis:
        given an expression and a final value domain, retrieves the original domain 
        (or bottom if this cannot happen)
    *)
    let rec bwd domain expr final = match expr with
    (* if the constant is in the value domain, then nothing changed, otherwise it cannot happen, hence bottom *)
    | CFG_int_const(a) -> if ValueDomain.subset (ValueDomain.const a) final then domain else bottom
    | CFG_int_rand(a, b) ->
      (* if the meeting of the random domain and the final is bottom, then no possible original domain can achieve this *)
      if ValueDomain.is_bottom (ValueDomain.meet final (ValueDomain.rand a b)) then
        bottom
      (* otherwise, everything's good *)
      else
        domain
    (* propagate *)
    | CFG_int_unary(op, expr) ->
      bwd domain expr (ValueDomain.bwd_unary (int_expr_to_value domain expr) op final )
    (* propagate into the graph *)
    | CFG_int_binary(op, e1, e2) ->
      let final1, final2  = ValueDomain.bwd_binary (int_expr_to_value domain e1) (int_expr_to_value domain e2) op final in
      let domain = bwd domain e1 final1 in
      bwd domain e2 final2
    (* similar to constant but instead we look for the value of the variable *)
    | CFG_int_var(var) ->
      let value = VarMap.find var domain in
      let meet_value = (ValueDomain.meet value final) in
      if ValueDomain.is_bottom meet_value then
        bottom
      else
        VarMap.add var meet_value domain
 
    let ast_op_not = function
    | AST_EQUAL         -> AST_NOT_EQUAL
    | AST_NOT_EQUAL     -> AST_EQUAL
    | AST_LESS          -> AST_GREATER_EQUAL
    | AST_LESS_EQUAL    -> AST_GREATER
    | AST_GREATER       -> AST_LESS_EQUAL
    | AST_GREATER_EQUAL -> AST_LESS
        
    let rec cfg_not = function
    (* simply switch the operator *)
    | CFG_compare(op, e1, e2) -> CFG_compare(ast_op_not op, e1, e2)
    | CFG_bool_unary(AST_NOT, b) -> b
    (* the negation of a value that can evaluate to both true and false can evaluate to both false and true *)
    | CFG_bool_rand -> CFG_bool_rand
    | CFG_bool_const(b) -> CFG_bool_const(not b)
    (* !(p && q) = !p || !q and !(p || q) = !p && !q *)
    | CFG_bool_binary(op, e1, e2) -> match op with
      | AST_AND -> CFG_bool_binary(AST_OR, cfg_not e1, cfg_not e2)
      | AST_OR -> CFG_bool_binary(AST_AND, cfg_not e1, cfg_not e2)

    (* abstract join *)
    let join dom1 dom2 =
      VarMap.fold (fun id value1 domain ->
        match VarMap.find_opt id dom2 with 
        | Some(value2) -> VarMap.add id (ValueDomain.join value1 value2) domain
        | None -> VarMap.add id value1 domain
      ) dom1 dom2
    
    (* abstract meet *)
    let meet dom1 dom2 =
      if is_bottom dom1 then bottom else
      VarMap.fold (fun id value1 dom ->
        if is_bottom dom then bottom
        else match VarMap.find_opt id dom2 with 
        | Some(value2) -> 
            let meeting = ValueDomain.meet value1 value2 in
            if ValueDomain.is_bottom meeting then bottom
            else VarMap.add id meeting dom
        | None -> bottom
      ) dom1 dom2

    (* filter environments to keep only those satisfying the boolean expression *)
    let rec guard domain = function
		| CFG_compare(op, e1, e2) ->
			begin
        let lfinal, rfinal = ValueDomain.compare (int_expr_to_value domain e1) (int_expr_to_value domain e2) op in
        let domain = bwd domain e1 lfinal in
        bwd domain e2 rfinal
			end
		| CFG_bool_unary(AST_NOT, b) -> guard domain (cfg_not b)
		| CFG_bool_binary(AST_AND, b1, b2) -> meet (guard domain b1) (guard domain b2)
		| CFG_bool_binary(AST_OR, b1, b2) -> join (guard domain b1) (guard domain b2)
    | CFG_bool_const(false) -> bottom
    (* constant true and random can both evaluate to true *)
    | _ -> domain
 
    (* widening *)
    let widen: t -> t -> t = failwith "unimplemented"
 
    (* narrowing *)
    let narrow: t -> t -> t = failwith "unimplemented"
 
    (* whether an abstract element is included in another one *)
    let subset dom1 dom2 =
      VarMap.fold 
      (fun var value is_subset ->
        if VarMap.mem var dom2 then (ValueDomain.subset value (VarMap.find var dom2)) && is_subset
        else false
      ) dom1 true

    (* prints *)
    let print formatter domain = 
    VarMap.iter (
      fun var value ->
        Format.fprintf formatter "%s <- " var.var_name;
        ValueDomain.print formatter value ;
        Format.fprintf formatter "\n"
    ) domain
end