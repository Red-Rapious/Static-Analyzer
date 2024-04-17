open Frontend
open Domain
open Cfg
open Value_domain

(*let rec satisfies_opt int_expr = function
| CFG_bool_unary (AST_NOT, bool_expr) -> 
  (match satisfies_opt int_expr bool_expr with
  | Some b -> Some (not b)
  | None -> None)
| CFG_bool_const b -> Some b
| CFG_bool_rand -> None
| _ -> failwith "unimplemented"

let satisfies int_expr bool_expr = 
match satisfies_opt int_expr bool_expr with 
| None -> true
| Some b -> b*)


module VarMap = Map.Make(Var)

module Concrete(Vars:VARS) : DOMAIN = functor (ValueDomain:VALUE_DOMAIN) ->
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
 
     (* filter environments to keep only those satisfying the boolean expression *)
     let guard  domain bool_expr = failwith "unimplemented"
      (*VarMap.filter (fun _ int_expr -> satisfies int_expr bool_expr) domain*)
 
     (* abstract join *)
     let join: t -> t -> t = failwith "unimplemented"
 
     (* abstract meet *)
     let meet: t -> t -> t = failwith "unimplemented"
 
     (* widening *)
     let widen: t -> t -> t = failwith "unimplemented"
 
     (* narrowing *)
     let narrow: t -> t -> t = failwith "unimplemented"
 
     (* whether an abstract element is included in another one *)
     let subset: t -> t -> bool = failwith "unimplemented"
 
     (* whether the abstract element represents the empty set *)
     let is_bottom: t -> bool = VarMap.is_empty
 
     (* prints *)
     let print: Format.formatter -> t -> unit = failwith "unimplemented"
end